#lang forge


// 16

sig Bool {}

abstract sig Process {
    ptable : one Pagetable
    st : one State
    // registers : set register
    pid : one Int
    // threads : set Thread
}

// sig register {}

abstract sig State {

}

one sig runnable extends State {}
one sig free extends State {}
one sig blocked extends State {}
one sig broken extends State {}

sig Page {
    //var active : lone Bool
    //var data : lone Bool
    var 
}

sig Pagetable extends Page {
    mapping : set Page -> Page

}
