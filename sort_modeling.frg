#lang forge
option run_sterling "layout.cnd"

sig State {}

sig IntNode {
    value: one Int,
    next: pfunc State -> IntNode
    // currNext: lone IntNode 
}

one sig LinkedList {
    head: one IntNode,
    firstState: one State,
    nextState: pfunc State -> State
}

fun next_pair[i1, i2: IntNode, s: State]: set (IntNode -> IntNode) {
  {i1,i2: IntNode| i1.next[s] = i2}
  // {i1.next[s] = i2}
}

fun state_pair[s1,s2:State, l: LinkedList]: set (State -> State) {
  {s1,s2: State | l.nextState[s1] = s2}
}

fun edges[s: State]: set (IntNode -> IntNode) {
  {i, j: IntNode | i.next[s] = j}
}

pred wellformed {
  
  all disj s, s2: State {
    // acyclic
  
    all l: LinkedList, i1,i2: IntNode | {
      // s != l.firstState implies {
      //   l.nextState[s] != l.firstState
      // }
      // s != l.firstState implies {reachable[s,l.firstState,state_pair[s,s2,l]]}
      // s = l.firstState implies {not reachable[s,l.firstState,state_pair[s,s2,l]]}

      l.nextState[s] != l.firstState and l.nextState[s2] != l.firstState
      l.nextState[s] != l.nextState[s2] and l.nextState[s] != s

      sorted[l.firstState]

      not reachable[i1, i1, next_pair[i1, i2, s]]
      // head is not reachable through any node
      // i1 != l.head implies not reachable[l.head, i1, next_pair[i1, i2, l.firstState]]
      i1 != l.head implies not reachable[l.head, i1, next_pair[i1, i2, s]]


      // all nodes are reachable from head
      // i1 != l.head implies reachable[i1,l.head,next_pair[i1,i2, l.firstState]]

      i1 != l.head and s != l.firstState implies reachable[i1,l.head,next_pair[i1,i2, s]]
    }
  }
}



pred sorted[s:State] {
  all i1,i2: IntNode|
      i1.next[s] = i2 implies i1.value <= i2.value
}


pred newInsertion {
  // you have some state, s and s' which is the state following the previous state
  // In s, there is a unique tail
  // In the first state, s, the newNode cannot reach the head via any edges
  // The next of the tail in s' is the newNode
  // Since that becomes the tail, there is no next for the newNode at s'
  // For all nodes minus the tail and the newNode, the next field in s' is the same as in s
  all l: LinkedList | {
    some s: State | {
      some i: IntNode | {
        one i2: IntNode | {
          i2 != i implies reachable[i,l.head,edges[l.firstState]]
          s = l.firstState
          no i.next[s] 
          i.next[l.nextState[s]] = i2
          no i2.next[l.nextState[s]]
          no i2.next[s]
          not reachable[i2,l.head,edges[s]]
          reachable[i2,l.head,edges[l.nextState[s]]]
        }
      }
    }
  }
}


---------------------------------------------------------------

pred someList {
    // some l: LinkedList | wellformed and sorted and newInsertion
    some l: LinkedList | wellformed and newInsertion
}
run {
  someList
 } for exactly 1 LinkedList, exactly 5 IntNode, exactly 3 State


 