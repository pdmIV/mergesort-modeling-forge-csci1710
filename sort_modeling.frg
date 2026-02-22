#lang forge/froglet

sig State {}
one sig Transition {
  firstState: one State,
  nextState: pfunc State -> State
}

sig IntNode {
    value: one Int,
    next: lone IntNode
}
sig LinkedList {
    head: one IntNode,
    currhead: pfunc State -> IntNode
}


pred wellformed {
  // acyclic
  all n: IntNode | not reachable[n, n, next]
  all l: LinkedList, some h, n: IntNode | h = l.head implies {
    n != h and not reachable[h, n, next]
  }
}

pred sorted {
  all n: IntNode |
    some n.next implies n.value <= n.next.value
}

pred permutation[a, b: IntArray] {
  all i: Int | (0 <= i and i <= a.lastIndex) implies
    some j: Int | (0 <= j and j <= b.lastIndex) and (a.elements[i] = b.elements[j])
  all j: Int | (0 <= j and j <= b.lastIndex) implies
    some i: Int | (0 <= i and i <= a.lastIndex) and (a.elements[i] = b.elements[j])
}

//sig MergeState {
    //arr: one IntArray // should become more sorted over time (assume ascending order is sorted)
//} {
    //validArray[arr]
//}


//pred someArray {
    //some a: IntArray | validArray[a]
//}
//run someArray for 5 Int, exactly 1 IntArray