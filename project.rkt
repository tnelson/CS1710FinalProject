#lang forge

option problem_type temporal
option max_tracelength 14 

abstract sig State {}
one sig RUNNABLE extends State {}
one sig FREE extends State {}
one sig BLOCKED extends State {}
one sig BROKEN extends State {}


// CHOICES: If/how to represent data in a page -- boolean flag, actual data, nothing?
// address field and next field? 
sig Page {
    address : one Int,
    next : lone Page
    //before : lone Page
    //var data : lone Bool
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
    mapping : set Int -> Page // Int -> Page or Int -> Int ?
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
    // Why ?? :( Come back to later
   // one(Kernel.ptable)
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
}

pred moves { 
    
}

pred traces { 
    initialState
    always(invariants)
}
// run {some(Pagetable) and some(Page)}

run{traces} for exactly 4 Page , exactly 4 UserProcess ,4 Int