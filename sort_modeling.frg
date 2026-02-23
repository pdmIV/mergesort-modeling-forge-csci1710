#lang forge
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
  all s: State| {
    let pair = {i1,i2: IntNode | i1.next[s] = i2} | {
      all i: IntNode, s: State | i.currNext = i.next[s]
      all s: State, n: IntNode | not reachable[n, n, pair]
    }
  }
  
  // all s: State, n: IntNode | not reachable[n, n, {i1,i2: IntNode | i1.next[s] = i2}]
  
  // for all s: State | 

  // head is not reachable from any node
  all l: LinkedList, n: IntNode | n != l.head implies not reachable[l.head, n, currNext]
  // all nodes are reachable from head
  all l: LinkedList, n: IntNode | n != l.head implies reachable[n, l.head, currNext]
}

pred sorted {
  all n: IntNode |
    some n.currNext implies n.value < n.currNext.value
}

// pred insertion {
//   all l: LinkedList | {
//     all n: IntNode | {
//       some s: State | {
//         reachable[n,l.head, currNext] implies {
//           some m: IntNode | n.next[l.nextState[s]] = m or l.head = m
//         }
//       }
//     } 
//   }
//   // if some state is reachable in the current time step from the head, then there exists some other node m in the state next and not equal to original elements
//   // for argument m to add ----> reachable[n,l.head,currNext]       there must be some n    n.next[next_state] = m
// }

pred insertion {
  all l: LinkedList | {
    some n: IntNode | {
      some s: State | {
        some m: IntNode| (n.next[l.nextState[s]] = m or l.head = m ) implies {
        //no m: IntNode | n.next[s] = m implies {
          n.next[s] != m
          //n.next[l.nextState[s]] = m or l.head = m
        }
      }
    } 
  }
  // if some state is reachable in the current time step from the head, then there exists some other node m in the state next and not equal to original elements
  // for argument m to add ----> reachable[n,l.head,currNext]       there must be some n    n.next[next_state] = m
}

// pred insertionV2 {
//   all l: LinkedList | {
//     all n: IntNode | {
//       some s: State | {
//         some m: IntNode | {
//           n.next[s] != m implies {
//             // MODIFY LINE BELOW TO INCLUDE HEAD
//             some node: IntNode | node.next[l.nextState[s]] = m // or l.head = m // do we need to clarify that node is reachable from head?
//           }
//         } 
//       }
//     } 
//   }


pred insertionV3 {
  all l: LinkedList | {
    all n: IntNode | {
      some s: State | {
        some m: IntNode | {
          not reachable[m,l.head,currNext] implies {
            reachable[m, l.head.next[l.nextState[s]], currNext]
          }
        } 
      }
    } 
  }
  // if some state is reachable in the current time step from the head, then there exists some other node m in the state next and not equal to original elements
  // for argument m to add ----> reachable[n,l.head,currNext]       there must be some n    n.next[next_state] = m
}


---------------------------------------------------------------

pred someList {
    some l: LinkedList | wellformed and sorted and insertionV3
}
run {
  someList
 } for 5 Int, exactly 1 LinkedList, exactly 5 IntNode, exactly 2 State