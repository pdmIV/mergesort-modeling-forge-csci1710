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

// test that sorted works
test suite for sorted {
  example sortedList is { sorted[`s1 & State] } for {
    LinkedList = `l
    State = `s1
    IntNode = `a + `b + `c

    `l.firstState = `s1

    `a.value = 1
    `b.value = 2
    `c.value = 3

    `a.next = `s1 -> `b
    `b.next = `s1 -> `c
    -- usually also bind `c.next` (e.g., no `c.next[`s1]) depending on your model
  }

  example unsortedList is { not sorted[`s1 & State] } for {
    LinkedList = `l
    State = `s1
    IntNode = `a + `b + `c

    `l.firstState = `s1

    `a.value = 2
    `b.value = 1
    `c.value = 3

    `a.next = `s1 -> `b
    `b.next = `s1 -> `c
  }
}

// test that newInsertion works
test suite for newInsertion {
}

// test that swap works
test suite for swapping {
}
