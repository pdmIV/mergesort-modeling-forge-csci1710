#lang forge/froglet
option run_sterling "layout.cnd"

sig State {}

sig IntNode {
    value: one Int,
    next: pfunc State -> IntNode,
    currNext: lone IntNode 
}

sig LinkedList {
    head: one IntNode,
    firstState: one State,
    nextState: pfunc State -> State
}

pred wellformed {
  // acyclic
  all i: IntNode, s: State | i.currNext = i.next[s]
  all s: State, n: IntNode | not reachable[n, n, currNext]
  // head is not reachable from any node
  all l: LinkedList, n: IntNode | n != l.head implies not reachable[l.head, n, currNext]
  // all nodes are reachable from head
  all l: LinkedList, n: IntNode | n != l.head implies reachable[n, l.head, currNext]
}

pred sorted {
  all n: IntNode |
    some n.currNext implies n.value <= n.currNext.value
}


// TODO: Refactor this
// pred permutation[a, b: IntArray] {
//   all i: Int | (0 <= i and i <= a.lastIndex) implies
//     some j: Int | (0 <= j and j <= b.lastIndex) and (a.elements[i] = b.elements[j])
//   all j: Int | (0 <= j and j <= b.lastIndex) implies
//     some i: Int | (0 <= i and i <= a.lastIndex) and (a.elements[i] = b.elements[j])
// }


pred someList {
    some l: LinkedList | wellformed and sorted
}
run someList for 5 Int, exactly 1 LinkedList, exactly 5 IntNode