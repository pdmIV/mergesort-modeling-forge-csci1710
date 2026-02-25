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
fun tail[l: LinkedList, s: State]: set IntNode {
  {t: IntNode |
    reachable[t, l.head, edges[s]] and no t.next[s]
  }
}
pred hasUniqueTail[l: LinkedList, s: State] {
  one tail[l, s]
}

pred sortedV2[l: LinkedList, s: State] {
  all i1, i2: IntNode | {
    (reachable[i1, l.head, edges[s]] and i1.next[s] = i2)
      implies i1.value <= i2.value
  }
}

pred wellformedV3 {
  all l: LinkedList | {
    sortedV2[l, l.firstState]
    all s: State | {
      // Acyclic
      all n: IntNode | not reachable[n, n, edges[s]]

      // Head is the root
      all n: IntNode | n.next[s] != l.head
    }
  }
}

pred wellformed {
  
  all s, s2: State {
    // acyclic
  
    all l: LinkedList, i1,i2: IntNode | {
      // s != l.firstState implies {
      //   l.nextState[s] != l.firstState
      // }
      s != l.firstState implies {reachable[s,l.firstState,state_pair[s,s2,l]]}
      s != l.firstState implies {not reachable[l.firstState,s,state_pair[s,s2,l]]}

      sorted[l.firstState]

      not reachable[i1, i1, next_pair[i1, i2, s]]
      // head is not reachable through any node
      // i1 != l.head implies not reachable[l.head, i1, next_pair[i1, i2, l.firstState]]
      i1 != l.head implies not reachable[l.head, i1, next_pair[i1, i2, s]]


      // all nodes are reachable from head
      // i1 != l.head implies reachable[i1,l.head,next_pair[i1,i2, l.firstState]]
      i1 != l.head implies reachable[i1,l.head,next_pair[i1,i2, s]]
    }
  }
}


// pred wellformedV2 {
//   // acyclic
//   all s: State| {
//     let pair = {i1,i2: IntNode | i1.next[s] = i2} | {
//       all i: IntNode, s: State | i.currNext = i.next[s]
//       all s: State, n: IntNode | not reachable[n, n, pair]
//     }
//   }
  
//   // all s: State, n: IntNode | not reachable[n, n, {i1,i2: IntNode | i1.next[s] = i2}]
  
//   // for all s: State | 

//   // head is not reachable from any node
//   all l: LinkedList, n: IntNode | n != l.head implies not reachable[l.head, n, currNext]
//   // all nodes are reachable from head
//   all l: LinkedList, n: IntNode | n != l.head implies reachable[n, l.head, currNext]
// }

pred sorted[s:State] {
  all i1,i2: IntNode|
    // all s | State { 
      i1.next[s] = i2 implies i1.value <= i2.value
    // }
    
    // some n.currNext implies n.value < n.currNext.value
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

pred newInsertion {
  all l: LinkedList | {
    all s: State | {
      some i1,i2,newNode: IntNode | {
        not reachable[newNode,i1, next_pair[i1,i2,s]] implies {
          some oldNode: IntNode | {
            reachable[oldNode,i1, next_pair[i1,i2,s]]
            reachable[newNode,oldNode, next_pair[i1,i2, l.nextState[s]]] // or l.head = newNode // this should be commented out later for robustness

            //if 


          }
        }
      }
    }
  }
}

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


// 
  // if some state is reachable in the current time step from the head, then there exists some other node m in the state next and not equal to original elements
  // for argument m to add ----> reachable[n,l.head,currNext]       there must be some n    n.next[next_state] = m



---------------------------------------------------------------

pred someList {
    // some l: LinkedList | wellformed and sorted and newInsertion
    //some l: LinkedList | wellformed //and newInsertion
}
run {
  someList
 } for 5 Int, exactly 1 LinkedList, exactly 3 IntNode, exactly 3 State


 