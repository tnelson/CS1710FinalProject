#lang forge

//Use electrum mode with trace length 14
option problem_type temporal
option max_tracelength 14 

/* ######################### */
/*          SIGS             */
/* ######################### */
//Notes : 
//safety and liveness for the scheduler -> all procs get turn 
//custom visualiser not mandatory but would be good -> upto your view on how sterling is looking 
//To DO : 
// Make sure init is working 

// The state of a given process
abstract sig State {}
one sig RUNNABLE extends State {}
one sig FREE extends State {}
one sig BLOCKED extends State {}
one sig BROKEN extends State {}

// Page permissions
abstract sig Permission {}
one sig READ extends Permission {} // read/view only 
one sig WRITE extends Permission {} // read and write 

/*
Add scheduler sig later
- schedules when processes are allowed to run
- when the process is running it may execute a move
*/

// CHOICES: If/how to represent data in a page -- boolean flag, actual data, nothing?
// address field and next field? 
sig Page {
    address : one Int,
    next : lone Page
    //var allocated : lone Bool // should we have this indicator?
}

// CHOICES: Should extend Page or not?
// If we extend page, not accurately representing virtual addresses
// If we don't extend page, we can't have a Page->Page mapping that
// encompasses virtual or physical pages
// Answer: have Address sig in addition to Page sig
// sig VMPage {  
//     //virtualAdrr : one Int
// }

// CHOICES:
// Should there be a `mapping` field at all? In a real system, a pagetable is not
// differntiable from a page; What makes most sense from a modelling perspective?
// First in relation: Int vs. Address sig for virtual memory?
// Second in relation: Page vs. Int sig for physical memory? 
sig Pagetable {
    var mapping : set Int -> Page, // Int -> Page or Int -> Int ?
    var permissions: set Page -> Permission
}

abstract sig Process {
    pid : one Int,
    var ptable : lone Pagetable,  // lone vs. one
    var st : one State, 
    var children : set Process

    // registers : set register
    // threads : set Thread
}
one sig Kernel extends Process {}
sig UserProcess extends Process {} 

/* ######################### */
/*           SETUP           */
/* ######################### */

// Set up the arrangement of physical memory.
// Ensures that there is a linear next relation
// that corresponds to addresses (addresses are in order).
pred SetupPhysicalMemory{
    no(next & iden)
    one p : Page | {
        p.^next = Page - p
        p.address = sing[0]
    }
    no(next & (~^next))
    all p : Page | {
        one(p.next) => p.next.address = sing[add[1,sum[p.address]]]
    }
}

// All User Processes are empty initially.
// Reminiscent of an array of processes that are waiting to be created.
pred initUserProc { 
    UserProcess.st = FREE
    pid.~pid in iden 
    no(UserProcess.ptable)
    no(children)  // enforce that we start with no children? yes... verify that a process can't have children after it's freed
    all p: UserProcess {
        sum[p.pid] <= #UserProcess
    }
}

pred initKernelProc {
    Kernel.st = RUNNABLE
    Kernel.pid = sing[0]
    no Kernel.children
    some Kernel.ptable
    // set up the kernel pagetable's mappings (identity mapping, uses 3 pages for kernel code)
    all p : Page | {
        // create mapping to all physical pages (except for page 0)
        sum[p.address] > 0 => Kernel.ptable.mapping[p.address] = p
        some Kernel.ptable.mapping.p => ~(Kernel.ptable.mapping)[p] = p.address
        // kernel code stored in first 3 pages (write permissions), read only otherwise
        sum[p.address] > 0 and sum[p.address] <= 3 => Kernel.ptable.permissions[p] = WRITE
        sum[p.address] > 3 => Kernel.ptable.permissions[p] = READ
    }
} 

pred emptyPageTables {
    all pt: Pagetable - Kernel.ptable | {
        no pt.mapping
        no pt.permissions
    }
}

// Initial state requirements for the processes
pred initialState {
    initKernelProc
    initUserProc
    emptyPageTables
}

pred invariants { 
    // number of pages?
    // number of virtual pages?
    // max amount of data in a page (if modelling that)
    // max number of mappings in a pagetable (if modelling that)
    SetupPhysicalMemory
    ptable.~ptable in iden 
    all i: Int {
        i in Page.address => sum[i] >= 0 // physical addresses
        i in Process.pid => sum[i] >= 0 // pids
        i in Pagetable.mapping.Page => sum[i] >= 0 // Virtual addresses
    }
    //Kernel Pagetable shouldn't change!
    (Kernel.ptable)' = Kernel.ptable
}

/* ######################### */
/*          HELPERS          */
/* ######################### */

// Checks if a physical page is in use by a UserProcess
pred allocated[p: Page]{
    some UserProcess.ptable.mapping.p 
}

// Checks if a virtual address of a particular process is in use
pred virtualAllocated[p: Process, addr: Int]{
    some p.ptable.mapping[addr]
}

/* ######################### */
/*           MOVES           */
/* ######################### */

/*
- initialize process
For running processes
- doNothing[p: Process]
- allocateMemory[p: Process]
- freeMemory[p: Process, adr: Int]
*/

pred initializeProcess[p: Process] {
    // p.st = FREE
    st' = st + p->RUNNABLE - p->FREE
    (p.st)' = RUNNABLE  //Rewriting this line from st' = st + .. to (p.st)' solved the UNSAT problem
    pid' = pid
    children' = children
    one((p.ptable'))
    // allocate 2 initial pages
    // You need to refer to the next Page table ptable' not current one!
    some pg : Page | {
        pg.address != sing[0]
        not allocated[pg]
        (p.ptable.mapping)' = pg.address->pg
        // ~(p.ptable.mapping)[pg] = pg.address  Why ? This seems unnecessary
        (p.ptable.permissions)' = pg->WRITE
    }
    //  #(p.ptable.mapping') = 2                                   // try commenting out this line
     all proc : Process  - p { 
         proc.ptable.mapping' = proc.ptable.mapping 
         proc.ptable.permissions' = proc.ptable.permissions
     }
}

pred allocateMemory[p: Process, adr: Int] {
    some pg: Page {
        not allocated[pg]
        mapping' = mapping + p.ptable->adr->pg
        permissions' = permissions + p.ptable->pg->WRITE // represents allocating heap memory -- writeable
    }
    st' = st
    pid' = pid
    children' = children
    ptable' = ptable
}

pred freeMemory[p: Process, adr: Int] {
    // once allocateMemory[p, adr] **This should be a property we verify about the system not enforce**
    virtualAllocated[p, adr]
    mapping' = mapping - p.ptable->adr->p.ptable.mapping[adr]
    permissions' = permissions - p.ptable->p.ptable.mapping[adr]->p.ptable.permissions[p.ptable.mapping[adr]]
    st' = st
    pid' = pid
    children' = children
    ptable' = ptable
}

pred moves { 
    always {
        some p1: Process | one adr: Int {
            initializeProcess[p1]   or allocateMemory[p1, adr] or freeMemory[p1, adr]                     // try running with just the initializeProcess option, shouldn't be unsat
        }
    }
}

pred traces { 
   initialState
   always(invariants)
    one p1: UserProcess  {
            initializeProcess[p1]   
    }
   //moves
 
    
}

// run {some(Pagetable) and some(Page)}
run{traces} for exactly 7 Page,exactly 3 UserProcess,4 Int

/* ######################### */
/*       VERIFICATION        */
/* ######################### */

/*
Model working properly
- processes never lose their pagetables
- free processes all eventually become runnable
Verification of important properties
- memory isolation
*/

pred isolation {
    
}