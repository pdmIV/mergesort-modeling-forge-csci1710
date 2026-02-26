#lang forge

open "sort_modeling.frg"


// still need to finish this :(


test suite for wellformed {
    example noEdges is not wellformed for {
        LinkedList = `l
        State = `s1
        IntNode = `a + `b + `c
        `l.firstState = `s1
        `a.next = `s1-> `b 
        `b.next = `s1 -> `c
    }
}
