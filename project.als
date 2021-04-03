#lang forge

option problem_type temporal
option max_tracelength 14 

/* ######################### */
/*          SIGS             */
/* ######################### */
//safety and liveness for the scheduler -> all procs get turn 
//custom visualiser not mandatory but would be good -> upto your view on how sterling is looking 
//To DO : 
// Make sure init is working 


abstract sig State {}
one sig RUNNABLE extends State {}
one sig FREE extends State {}
one sig BLOCKED extends State {}
one sig BROKEN extends State {}

/*
Add scheduler sig later
- schedules when processes are allowed to run
- when the process is running it may execute a move
*/

sig Bool {}

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
sig Pagetable extends Page {
    var mapping : set Int -> Page // Int -> Page or Int -> Int ?
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
}

pred initKernelProc {
    Kernel.st = RUNNABLE
    Kernel.pid = sing[0]
    no Kernel.children
    one(Kernel.ptable) -- UNSAT
    all p : Page - Pagetable | {
        sum[p.address] < 3 => p.address -> p in Kernel.ptable.mapping // < 3 seems to be making lots of assumptions ab memory layout...
        sum[p.address] > 3 => not (p.address -> p in Kernel.ptable.mapping)
    }
} 

// Initial state requirements for the processes
pred initialState {
    initKernelProc
    initUserProc
}

pred invariants { 
    // number of pages?
    // number of virtual pages?
    // max amount of data in a page (if modelling that)
    // max number of mappings in a pagetable (if modelling that)
    SetupPhysicalMemory
    all i: Int{
        i in Page.address => sum[i] >= 0 // physical addresses
        i in Process.pid => sum[i] >= 0 // pids
        i in Pagetable.mapping.Page => sum[i] >= 0 // Virtual addresses
    }
}

/* ######################### */
/*          HELPERS          */
/* ######################### */

// Checks if a physical page is in use
pred allocated[p: Page]{
    p in Process.ptable or some Pagetable.mapping.p 
}

// Checks if a virtual address of a particular process is in use
pred virtualAllocated[p: Process, addr: Int]{
    some p.ptable.mapping[addr]
}

/* ######################### */
/*           MOVES           */
/* ######################### */

/*
- doNothing[p: Process]
- allocateMemory[p: Process]
- freeMemory[p: Process, adr: Int]
*/

pred doNothing[p: Process]{
    p.pid' = p.pid
    p.ptable' = p.ptable
    p.st' = p.st
    p.children' = p.children
}

pred allocateMemory[p: Process, adr: Int]{
    p.st = RUNNABLE
    one page: Page {
        not page in Pagetable 
        not allocated[page]
        p.ptable.mapping' = p.ptable.mapping + adr->page
    }
    pid' = pid
    st = st'
    children = children'
}

pred freeMemory[p: Process, adr: Int]{
    p.st = RUNNABLE
    pid' = pid
    st = st'
    children = children'
    // once allocateMemory[p, adr] **This should be a property we verify about the system not enforce**
    virtualAllocated[p, adr]
    p.ptable.mapping' = p.ptable.mapping - adr->Page

}

pred moves { 
    {
        some p1: Process {
            one adr: Int {
                not virtualAllocated[p1, adr]
                allocateMemory[p1, adr] or freeMemory[p1 , adr]
            }
            all p2: Process {
                p1 != p2 => doNothing[p2]
            }
        }
    }
}

pred traces { 
    initialState
    moves
    always(invariants)
}

// run {some(Pagetable) and some(Page)}
run{traces} for exactly 1 Pagetable, exactly 4 Page, exactly 4 UserProcess, 4 Int

/* ######################### */
/*       VERIFICATION        */
/* ######################### */

pred isolation {
    
}