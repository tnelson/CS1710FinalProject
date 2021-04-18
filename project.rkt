#lang forge

//Use electrum mode with trace length 14
option problem_type temporal
option max_tracelength 14 

/* ######################### */
/*          SIGS             */
/* ######################### */
// The state of a given process
abstract sig State {}
// A process is running 
one sig RUNNABLE extends State {}
// A process slot is free and empty 
one sig FREE extends State {}
//The process is blocked
one sig BLOCKED extends State {}
//The process has crashed 
one sig BROKEN extends State {}

// Page permissions
abstract sig Permission {}
one sig READ extends Permission {} // read/view only 
one sig WRITE extends Permission {} // read and write 

/*
*A page is the smallest unit of memory we consider in order to actually model an interesting system in Forge
* This is also very realistic as a Page is usually the smallest unit of memory allocated to processes.
* Memory is tracked by the kernel in units of pages 
* Here our sig has two fields - 
* address : Each page has an integer address 
* next : Each page has a page that comes strictly after it. This is intended to model the sequential nature of memory. 
*/ 
sig Page {
    address : one Int,
    next : lone Page
}
/*
*A pagetable is the data structure that stores the mapping from a processes's virtual memory to the actualy physical memory address
* Each running process has an associated pagetable
* mapping : The mapping from integer Virtual Addresses to physical pages
* permissions : For each page can the process only read or can it read and write to the page ? 
*/
sig Pagetable {
    var mapping : set Int -> Page, 
    var permissions: set Page -> Permission
}

/*
A Process that runs on the system 
pid : The unique Process id 
ptable : The pagetable for the process
st : The current state of the process
 */
abstract sig Process {
    pid : one Int,
    var ptable : lone Pagetable, 
    var st : one State
}
/* 
The Kernel is the OS Kernel that runs with privelages mode. It can access all pages
UserProcess are the rest of processes that run on the system. They have restrictions and are restricted to only 
the pages provided to it by the Kernel. 
*/
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

/* 
UserProcess are an array of processes waiting to be intialized and run 
In the initial state all of them are free and don't have an associated pagetable 
*/
pred initUserProc { 
    UserProcess.st = FREE
    pid.~pid in iden 
    no(UserProcess.ptable)
    all p: UserProcess {
        sum[p.pid] <= #UserProcess
    }
}
/*
The Kernel is running in the beginning 
It also has the process id 0 , and has a pagetable with mappings to all the pages in memory
*/
pred initKernelProc {
    Kernel.st = RUNNABLE
    Kernel.pid = sing[0]
    some Kernel.ptable
    // set up the kernel pagetable's mappings (identity mapping, uses 3 pages for kernel code)
    all pg : Page | {
        sum[pg.address] = 0 => no Kernel.ptable.mapping.pg and no Kernel.ptable.permissions[pg]
        // create mapping to all physical pages (except for page 0)
        sum[pg.address] > 0 => Kernel.ptable.mapping[pg.address] = pg
        some Kernel.ptable.mapping.pg=> ~(Kernel.ptable.mapping)[pg] = pg.address
        // kernel code stored in first 3 pages (write permissions), read only otherwise
        sum[pg.address] > 0 and sum[pg.address] <= 3 => Kernel.ptable.permissions[pg] = WRITE
        sum[pg.address] > 3 => Kernel.ptable.permissions[pg] = READ
    }
} 
/*
*All the Page tables expect the Kernel's are empty in the beginning
*/
pred emptyPageTables {
    all pt: Pagetable - Kernel.ptable | {
        no pt.mapping
        no pt.permissions
    }
}

// This predicate puts together all the predicates which specify the intialState
pred initialState {
    initKernelProc
    initUserProc
    emptyPageTables
}
/*
invariants encapsulates all the things we want to hold true throughout all states
These include : 
*The physical memory page setup
* The kernel pagetable being the same (Should we be verifying this instead ? No , because if we didn't specify it here we would have to do so in 
all the state change predicates)
*/
pred invariants { 
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

/* Checks if a physical page is in use
  in use = some process has write permissions
*/
pred allocated[pg: Page]{
    pg.address = sing[0] or (WRITE in Process.ptable.permissions[pg]) // pg can also be readable from other processes
}

// Checks if a virtual address of a particular process is in use
pred virtualAllocated[p: Process, addr: Int]{
    some p.ptable.mapping[addr]
}

/* ######################### */
/*           MOVES           */
/* ######################### */

/* 
We model 4 primary state changes : 
1. A Process is intialized : A process goes from free to now running and now has a pagetable with maps to its allocated memory
2. Memory is allocated : An intialized process get's some more memory allocated to it
3. Memory is freed  : Some memory allocated to a process is freed
4. A Process is deleted : A process is done and is then deleted (it's memory is freed and page table is deleted) 
Through these 4 moves we capture the core of the process lifecyle and the associated memory management

*/

/*
deleteProcess frees a running process freeing the associated memory and deleting its pagetable 
*/

pred deleteProcess[p: Process] {
    p.st =  RUNNABLE
    st' = st + p->FREE - p->RUNNABLE
    ptable' = ptable - p->p.ptable
    mapping' = mapping - p->p.ptable->Int
    permissions' = permissions - p->p.ptable->Page

    /*
    // Other processes stay the same
    all pt : Pagetable | {
        no (ptable').pt => no pt.(mapping')
        no (ptable').pt => no pt.(permissions')
    }

    all proc : Process  - p { 
        proc.ptable = proc.ptable'
        proc.ptable.mapping' = proc.ptable.mapping 
        proc.ptable.permissions' = proc.ptable.permissions
    }
    */
}
/*Sets up a process giving it a pagetable and a starting memory allocation of 2 Pages */
pred initializeProcess[p: Process] {
    p.st = FREE
    st' = st + p->RUNNABLE - p->FREE
    (p.st)' = RUNNABLE  
    one pt: Pagetable{
        ptable' = ptable + p->pt
    }
    // allocate 2 initial pages
    // You need to refer to the next Page table ptable' not current one!

    all i: Int{ // Map first two virtual addresses
        ((sum[i] = 1) or (sum[i] = 2)) => 
            {
                one pg: Page | {
                    not allocated[pg] 
                    p.(ptable').(permissions')[pg] = WRITE
                    p.(ptable').(mapping')[i] = pg
                    p.(ptable').(mapping').pg = i
                } 
            } else {
                no p.ptable.mapping[i]'
            }
    }

    all pg: Page{
        (not (pg in p.ptable.mapping[Int]')) => no p.ptable.permissions[pg]'
    }

    all pt : Pagetable | {
        no (ptable').pt => no pt.(mapping')
        no (ptable').pt => no pt.(permissions')
    }
    //other processes do not change
    all proc : Process  - p { 
        proc.ptable = proc.ptable'
        proc.ptable.mapping' = proc.ptable.mapping 
        proc.ptable.permissions' = proc.ptable.permissions
    }
}
// A process requests some additional memory at adr which is then allocated assuming it's available
// Mapping to that address is then added to it's pagetable
pred allocateMemory[p: Process, adr: Int] {
    some pg: Page {
        not allocated[pg]
        mapping' = mapping + p.ptable->adr->pg
        permissions' = permissions + p.ptable->pg->WRITE // represents allocating heap memory -- writeable
    }
    st' = st
    ptable' = ptable
}
/*
Frees memory allocated to the process. Removes it from the processes pagetable 
*/

pred freeMemory[p: Process, adr: Int] {
    // once allocateMemory[p, adr] **This should be a property we verify about the system not enforce**
    virtualAllocated[p, adr]
    mapping' = mapping - p.ptable->adr->p.ptable.mapping[adr]
    permissions' = permissions - p.ptable->p.ptable.mapping[adr]->p.ptable.permissions[p.ptable.mapping[adr]]
    st' = st
    ptable' = ptable
}
/*
Enforces all the moves a system can make at any given time which are:
intializeProcess
deleteProcess
allocateMemory (To a certain process)
freeMemory (from a  certain process)
*/

pred moves { 
    always {
        (some p: Process - Kernel | initializeProcess[p] or deleteProcess[p]) or (some p: Process - Kernel | one adr: Int { allocateMemory[p, adr] or freeMemory[p, adr] } )
        /*some p1: Process - Kernel | one adr: Int { // Process vs. UserProcess
            // try running with just the initializeProcess option, shouldn't be unsat
            initializeProcess[p1] or allocateMemory[p1, adr] or freeMemory[p1, adr]
        }*/
    }
}
/*The traces predicate brings together the system
*It enforces the intial state, the system invariants as well as the possible moves
*/
pred traces { 
   initialState
   always(invariants)
   moves            
   
}

//run{traces} for exactly 8 Page, exactly 3 UserProcess, 5 Int

// run {some(Pagetable) and some(Page)}


/* ######################### */
/*        INSTANCES          */
/* ######################### */

// A sample instance that our system generates
inst allProcesses {

    // Set Up
    Process = UserProcess0 + UserProcess1 + UserProcess2 + Kernel0
    UserProcess = UserProcess0 + UserProcess1 + UserProcess2
    Kernel = Kernel0
    Page = Page0 + Page1 + Page2 + Page3 + Page4 + Page5 + Page6 + Page7
    Pagetable = Pagetable0 + Pagetable1 + Pagetable2 + Pagetable3
    
    BROKEN = BROKEN0
    WRITE = WRITE0
    BLOCKED = BLOCKED0
    RUNNABLE = RUNNABLE0
    FREE = FREE0
    READ = READ0
    State = BROKEN0 + BLOCKED0 + RUNNABLE0 + FREE0
    Permission = WRITE0 + READ0
    pid = Kernel0->0 + UserProcess0->3 + UserProcess1->2 + UserProcess2->1

    address = Page0->7 + Page1->6 + Page2->5 + Page3->4 + Page4->3 + 
    Page5->2 + Page6->1 + Page7->0
    next = Page1->Page0 + Page2->Page1 + Page3->Page2 + Page4->Page3 + 
    Page5->Page4 + Page6->Page5 + Page7->Page6
    
    // State 1
    mapping = Pagetable3->1->Page6 + Pagetable3->2->Page5 + 
    Pagetable3->3->Page4 + Pagetable3->4->Page3 + Pagetable3->5->Page2 + 
    Pagetable3->6->Page1 + Pagetable3->7->Page0
    st = Kernel0->RUNNABLE0 + UserProcess0->FREE0 +  UserProcess1->FREE0 + UserProcess2->FREE0
    ptable = Kernel0->Pagetable3
    permissions = Pagetable3->Page0->READ0 + Pagetable3->Page1->READ0 + Pagetable3->Page2->READ0 + 
    Pagetable3->Page3->READ0 + Pagetable3->Page4->WRITE0 + Pagetable3->Page5->WRITE0 + Pagetable3->Page6->WRITE0

    // State 2 (init UserspaceProcess0)
    mapping' = Pagetable3->1->Page6 + Pagetable3->2->Page5 + 
    Pagetable3->3->Page4 + Pagetable3->4->Page3 + Pagetable3->5->Page2 + 
    Pagetable3->6->Page1 + Pagetable3->7->Page0 + Pagetable2->(1->Page3 + 2->Page2)
    st' = Kernel0->RUNNABLE0 + UserProcess0->RUNNABLE0 +  UserProcess1->FREE0 + UserProcess2->FREE0
    ptable'= Kernel0->Pagetable3 + UserProcess0->Pagetable2
    permissions' = Pagetable3->Page0->READ0 + Pagetable3->Page1->READ0 + Pagetable3->Page2->READ0 + 
    Pagetable3->Page3->READ0 + Pagetable3->Page4->WRITE0 + Pagetable3->Page5->WRITE0 + Pagetable3->Page6->WRITE0
    + Pagetable2->(Page3->WRITE0 + Page2->WRITE0)

    //initializeProcess[p1]
    //after initializeProcess[p2]
    //after after initializeProcess[p3]
    //after after after deleteProcess[p1]
    //after after after after deleteProcess[p2]
    //after after after after after deleteProcess[p3]

}
//run{allProcesses and traces} for exactly 8 Page, exactly 3 UserProcess, 5 Int


/* ######################### */
/*       VERIFICATION        */
/* ######################### */

/* This section models all the properties we verify about our system */
/*
Model working properly
- processes never lose their pagetables
- free processes all eventually become runnable
Verification of important properties
- memory isolation
- processes can be initialized and allocate or free memory
- VA space - process can only access memory in ptable
*/

pred invariance {
    SetupPhysicalMemory
    Kernel.ptable' = Kernel.ptable
    Kernel.ptable.mapping' = Kernel.ptable.mapping
    Kernel.ptable.permissions' = Kernel.ptable.permissions
    Kernel.st' = Kernel.st
}
// No two processes should every have access to the same page
pred isolation {
    all p1, p2: Process | all pg: Page {
        p1 != p2 => {
            not (WRITE in p1.ptable.permissions[pg] and WRITE in p2.ptable.permissions[pg])
        }
    }
}
//?
pred safety {
    all p: UserProcess {
        initializeProcess[p] => {
            p.st = FREE
            p.st' = RUNNABLE
            no p.ptable
            some p.ptable'
        }
        deleteProcess[p] => {
            p.st = RUNNABLE
            p.st' = FREE
            some p.ptable
            no p.ptable'
        }
    }
    all p: UserProcess | some adr: Int { 
        allocateMemory[p, adr] => {
            some p.ptable
            some p.ptable'
            no p.ptable.mapping[adr]
            some p.ptable.mapping[adr]'
            no p.ptable.permissions[p.ptable.mapping[adr]]
            p.ptable.permissions[p.ptable.mapping[adr]]' = WRITE
        }
        freeMemory[p, adr] => {
            some p.ptable
            some p.ptable'
            some p.ptable.mapping[adr]
            no p.ptable.mapping[adr]'
            p.ptable.permissions[p.ptable.mapping[adr]] = WRITE
            no p.ptable.permissions[p.ptable.mapping[adr]]'
        }
    }
}

pred isolatedVAspaces {
    all p1, p2: Process | all adr: Int {
        p1 != p2 => {
            // If process 1 has a VA that maps to a page accessible by process 2
            some p1.ptable.mapping[adr] and p1.ptable.mapping[adr] in p2.ptable.mapping[Int] => {
                // Then, process 1 and process 2 cannot have the same permissions on that page
                p1.ptable.permissions[p1.ptable.mapping[adr]] != p2.ptable.permissions[p1.ptable.mapping[adr]]
            }
        }
    }
}

pred VASpacesCanOverlap {
    some p1, p2: Process | some adr: Int {
        p1 != p2 => {
            // Processes map same VA to different pages
            p1.ptable.mapping[adr] != p2.ptable.mapping[adr]
        }
    }
}

pred procInitializedAndDeleted {
    some p: UserProcess {
        eventually initializeProcess[p]
        eventually deleteProcess[p]
    }
}

pred pageAllocatedAndFreed {
    some p: UserProcess | some adr: Int {
        eventually allocateMemory[p, adr]
        eventually freeMemory[p, adr]
    }
}

pred allocateToUnititializedProc {
    some p: UserProcess | some adr: Int {
        always not initializeProcess[p]
        eventually allocateMemory[p, adr]
    }
}
// Free memory from a process that is not initialized
pred freeFromUnititializedProc {
    some p: UserProcess | some adr: Int {
        always not initializeProcess[p]
        eventually freeMemory[p, adr]
    }
}

// concrete `sat`/`unsat` testing
test expect {
    vacuity: {traces} for exactly 7 Page, exactly 1 UserProcess, 4 Int is sat
    {traces and VASpacesCanOverlap} for exactly 7 Page, exactly 1 UserProcess, 4 Int is sat
    {traces and procInitializedAndDeleted} for exactly 7 Page, exactly 1 UserProcess, 4 Int is sat
    {traces and allocateToUnititializedProc} for exactly 7 Page, exactly 1 UserProcess, 4 Int is unsat
    {traces and freeFromUnititializedProc} for exactly 7 Page, exactly 1 UserProcess, 4 Int is unsat
}


// verification `theorem` testing
test expect {
    isolation_: {traces and not always isolation} for exactly 7 Page, exactly 1 UserProcess, 4 Int is unsat
    invariance_: {traces implies always invariance} for exactly 7 Page, exactly 1 UserProcess, 4 Int is theorem
    safety_: {traces implies always safety} for exactly 7 Page, exactly 1 UserProcess, 4 Int is theorem
    isolatedVAspaces_: {traces implies always isolatedVAspaces} for exactly 7 Page, exactly 1 UserProcess, 4 Int is theorem
}

