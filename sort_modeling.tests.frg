#lang forge

open "sort_modeling.frg"

// DO NOT EDIT ABOVE THIS LINE

test suite for edges {
    example noEdges is not wellformed for {
        LinkedList = `l
        State = `s1 + `s2
        IntNode = `a + `b + `c
        `l.firstState = `s1
        `a.next = `s1-> `b 
        `b.next = `s1 -> `c
    }
}
