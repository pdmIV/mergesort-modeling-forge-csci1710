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
fun totalNodes[s: State]: set IntNode {
  { n: IntNode | n = LinkedList.head[s] or reachable[n, LinkedList.head[s], edges[s]] }
}

test suite for newInsertion {

  example insertion_increases_length_by_one is {
    wellformed and newInsertion

    let s  = (`s1 & State) | {
      let nx = (`s2 & State) | {
      #(totalNodes[nx]) = #(totalNodes[s]) + 1
      }
    }

  } for {
    LinkedList = `l
    State      = `s1 + `s2
    IntNode    = `a + `b + `c + `d

    `l.firstState = `s1
    `l.nextState  = `s1 -> `s2

    `l.head = `s1 -> `a + `s2 -> `a

    `a.value = 1
    `b.value = 2
    `c.value = 3
    `d.value = 4

    `a.next = `s1 -> `b + `s2 -> `b
    `b.next = `s1 -> `c + `s2 -> `c
    `c.next = `s2 -> `d
  }
}

// test that swap works
test suite for swapping {
}
