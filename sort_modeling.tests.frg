#lang forge

open "sort_modeling.frg"


pred cycle {
  all s: State | {
    some i: IntNode| {i.next[s] = i} or reachable[i,i,edges[s]]
  }
  
}

pred unsorted {
  all disj i,j: IntNode | i.next[LinkedList.firstState] = j and i.value < j.value
}

//all nodes reachable from first state
pred allReachable {
  all i: IntNode| i=LinkedList.head[LinkedList.firstState] or reachable[i,LinkedList.head[LinkedList.firstState],edges[LinkedList.firstState]]
}

//ensure that once a list is sorted it never unsorts
pred staysSorted {
  no s: State | {
    all i: IntNode | reachable[i,LinkedList.head[s],edges[s]] implies sorted[s] and not sorted[LinkedList.nextState[s]]
  }
}

//if the head's successor is smaller than the head, then the head in the next state should swap to the smaller node
//works under our assumptions that the list is always sorted except for one node
pred headSwap {
  no s: State | {
    some i: IntNode | {
      i = LinkedList.head[s].next[s]
      LinkedList.head[s].value > i.value
      LinkedList.head[LinkedList.nextState[s]] = LinkedList.head[s]
    }
    
  }
}

//there exists some case where swapping is valid
pred swappingValid {
  some s: State | {
    s != LinkedList.firstState
    sorted[LinkedList.firstState]
    not sorted[LinkedList.nextState[LinkedList.firstState]] implies {
      sorted[s]
    }
  } 
}

//frame conditions hold
pred framed {
  all i: IntNode, s: State | {
    some LinkedList.nextState[s] implies {
      i.next[s].value > i.value implies {
        i.next[LinkedList.nextState[s]] = i.next[s]
      }
    }
  }
}

pred distinct{all disj i,j: IntNode | {i.value = j.value}}

//____________________________________________________________________________________________________

//simple test for distinct values
distinctCheck: assert distinct and distinctValues is unsat for exactly 1 LinkedList, exactly 2 IntNode


test suite for wellformed {
    //test that exactly one state is not valid
    example noSeparateNode is not wellformed for {
        LinkedList = `l
        State = `s1 + `s2
        IntNode = `a + `b + `c
        `l.firstState = `s1
        `a.next = `s1-> `b 
        `b.next = `s1 -> `c
    }

    //there needs to exist some second state
    example noSecondState is not wellformed for {
        State = `s1
        LinkedList = `l
        IntNode = `a + `b + `c
        `l.firstState = `s1
        `a.next = `s1-> `b 
    }

    //first state must be sorted
    unsortedFirstState: assert unsorted and wellformed is unsat for exactly 1 LinkedList, exactly 1 State, exactly 2 IntNode

    //no cycles
    noCycles: assert cycle and wellformed is unsat for exactly 1 LinkedList
}

// test that sorted works
test suite for sorted {
  example sortedList is {some s: State | s = `s1 and sorted[s] } for {
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

  example unsortedList is {some s: State | s = `s1 and not sorted[s] } for {
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

test suite for newInsertion {
  example insertion_increases_length_by_one is {
    wellformed and newInsertion

    some s : State | {
      s = `s1
      some nx : State| {
        nx = `s2
        some c,d: IntNode | {
          c = `c
          d = `d
          no c.next[s]
          c.next[nx] = d
        }
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

  //if all nodes are reachable from the first state, then we shouldnt be able to add new nodes
  noNewNode: assert {newInsertion and allReachable} is unsat for exactly 1 LinkedList
}

// test that swap works
test suite for swapping {
  // for swapping it is enough to show that we start from a valid state, move to an unsorted state, end in a sorted state, and our frame conditions hold
  // this works provided we run with more states than intnodes (allow O(N) time for insertion)
  validSwap: assert {swappingValid and wellformed and newInsertion and swapping} is sat for exactly 1 LinkedList
  frameCondition: assert {framed and wellformed and newInsertion and swapping} is sat for exactly 1 LinkedList

  //list always stays sorted after sorting once
  staySorted: assert {staysSorted and wellformed} is sat for exactly 1 LinkedList

  //the head correctly swaps
  swapHead: assert {headSwap and wellformed and newInsertion and swapping} is sat for exactly 1 LinkedList

}
