#lang forge
option run_sterling "layout.cnd"

sig State {}

sig IntNode {
    value: one Int,
    next: pfunc State -> IntNode 
}

one sig LinkedList {
    head: pfunc State -> IntNode,
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

pred distinctValues { // for visual clarity and to make the problem more interesting, we are forcing all nodes to be unique
  all disj a, b: IntNode | a.value != b.value
}

// Idea
fun succ[s: State]: lone State { LinkedList.nextState[s] }

fun headAt[s: State]: lone IntNode { LinkedList.head[s] }

fun insertedNode: lone IntNode {
  let s0 = LinkedList.firstState |
  let s1 = succ[s0] |
    { n: IntNode |
        some s1 and
        not (headAt[s0] != none or reachable[n, headAt[s0], edges[s0]]) and
        (headAt[s1] != none or reachable[n, headAt[s1], edges[s1]])
    }
}

pred bubbleInsertedOneStep[s: State] {
  let s2 = succ[s] | {
    some s2
    let x = insertedNode | {
        some x and (headAt[s] != none or reachable[x, headAt[s], edges[s]])

        // find predecessor p of x in s (p.next[s] = x)
        one p: IntNode | p.next[s] = x and {

          // only swap if out of order with predecessor
          x.value < p.value implies {
            // swap p and x
            p.next[s2] = x.next[s]
            x.next[s2] = p

            // rewire predecessor-of-p (or head) to point to x
            (headAt[s] = p) implies {
              LinkedList.head[s2] = x
            }
            (headAt[s] != p) implies {
              one pp: IntNode | pp.next[s] = p and pp.next[s2] = x
              LinkedList.head[s2] = LinkedList.head[s]
            }

            // frame everything else
            all n: IntNode - (p + x) | n.next[s2] = n.next[s]
          }

          // if not out-of-order, do nothing (stutter)
          not (x.value < p.value) implies {
            LinkedList.head[s2] = LinkedList.head[s]
            all n: IntNode | n.next[s2] = n.next[s]
          }
        }
      }
  }
}

pred swappingForced {
  let s0 = LinkedList.firstState | {
    let s1 = succ[s0] | {
      some s1
      all s: State - (s0) | {
        // only constrain transitions that exist along the linear trace
        (some succ[s]) implies {
          // start bubbling from s1 onward
          (s = s0) implies true
          (s != s0) implies bubbleInsertedOneStep[s]
        }
      }
    }
  }
}

--------------------------------------------------------------------------------------
pred wellformed {
  all s: State| {LinkedList.nextState[s] != s}
  
  all disj s, s2: State {
    // acyclic
  
    all l: LinkedList, i1,i2: IntNode | {
      distinctValues
      
      s != l.firstState implies {reachable[s,l.firstState,state_pair[s,s2,l]]}
      l.nextState[l.firstState] != none // just need to force a second state to exist

      l.nextState[s] != l.firstState and l.nextState[s2] != l.firstState
      l.nextState[s] != l.nextState[s2] and l.nextState[s] != s

      sorted[l.firstState]

      not reachable[i1, i1, next_pair[i1, i2, s]]
      // head is not reachable through any node
      // i1 != l.head implies not reachable[l.head, i1, next_pair[i1, i2, l.firstState]]
      i1 != l.head[s] implies not reachable[l.head[s], i1, next_pair[i1, i2, s]]
      i2 = i1.next[s] implies {no i3: IntNode | {i3 != i1 and i2 = i3.next[s]}}


      // all nodes are reachable from head
      // i1 != l.head implies reachable[i1,l.head,next_pair[i1,i2, l.firstState]]

      i1 != l.head[l.firstState] and s != l.firstState implies reachable[i1,l.head[l.firstState],next_pair[i1,i2, s]]

      s = l.firstState implies {one i : IntNode | not reachable[i,l.head[s],edges[s]] and i!= l.head[s]}
    }
  }
}



pred sorted[s:State] {
  all i1,i2: IntNode|
      i1.next[s] = i2 implies i1.value < i2.value
}

pred newInsertionV2 {
  let s = LinkedList.firstState | {
    let nx = LinkedList.nextState[s] {
      some nx
      some newNode: IntNode {
        not reachable[newNode, LinkedList.head[s], edges[s]]
        newNode != LinkedList.head[s]
        one tail: IntNode | {
          reachable[tail, LinkedList.head[s], edges[s]]
          no tail.next[s]

          tail.next[nx] = newNode
          no newNode.next[nx]

          all n: IntNode - tail - newNode | n.next[nx] = n.next[s]
        }
      }
    }
  }
}

// pred swapping {
//   // There may exist some integer which is out of order
//   // That integer swaps left in the next state if the node to the left has a value greater than that node
//   // Frame condition: The next field of all nodes unaffected by the swap are the same

//   // state cannot be FirstState because first state has not inserted the out of order element and thus is sorted

//   all s: State - (LinkedList.firstState + LinkedList.nextState[LinkedList.firstState]) | {  
//     // i.next[s].value < i.value
//     not sorted[s] implies {
//       one i: IntNode | {
//         i.next[s].value < i.value
//         i.next[LinkedList.nextState[s]] = i.next[s].next[s]
//         i.next[s].next[LinkedList.nextState[s]] = i

//         // i is not the head
//         some j:IntNode | j.next[s] = i and {
//           j.next[LinkedList.nextState[s]] = i.next[s]

//           //frame condition --> since there is a previous node, we also frame the head since this node cannot be the head
//           LinkedList.head[s] = LinkedList.head[LinkedList.nextState[s]]
//           all n: IntNode - (i + j + i.next[s]) | n.next[LinkedList.nextState[s]] = n.next[s]
//         } else {
//           // i is the new head of the list


//           //need some sort of predicate to handle the case where the head has to swap with another node
//           i = LinkedList.head[s] implies i.next[s] = LinkedList.head[LinkedList.nextState[s]]
          
//           // a -> c -> b
//           // a -> b -> c
//           //frame condition
//           all n: IntNode - (i + i.next[s]) | n.next[LinkedList.nextState[s]] = n.next[s]
//         }
//       }
//     } else {
//       all i: IntNode,s:State | {
//         reachable[i,LinkedList.head[s],edges[s]] implies i.next[s] = i.next[LinkedList.nextState[s]]
//       }
//     }
//   }
// }
  







// pred swappingV3 {
//   all s: State - (LinkedList.firstState + LinkedList.nextState[LinkedList.firstState]) | {
    
//     not sorted[s] implies {
//       some i: IntNode | {
//         i.next[s].value < i.value // The out-of-order condition
        
//         // CASE 1: 'i' is the head of the list
//         (LinkedList.head[s] = i) implies {
//           // Update the head pointer to the new first node
//           LinkedList.head[LinkedList.nextState[s]] = i.next[s]
          
//           // Perform the swap (A and B)
//           i.next[LinkedList.nextState[s]] = i.next[s].next[s]
//           i.next[s].next[LinkedList.nextState[s]] = i
          
//           // Frame the rest of the nodes
//           all n: IntNode - (i + i.next[s]) | n.next[LinkedList.nextState[s]] = n.next[s]
//         } 
//         else {
//         // CASE 2: 'i' is strictly inside the list (your original logic, corrected)
//           some j: IntNode | {
//             j.next[s] = i
            
//             // Frame the head since it's unaffected
//             LinkedList.head[LinkedList.nextState[s]] = LinkedList.head[s]
            
//             // Perform the swap
//             i.next[LinkedList.nextState[s]] = i.next[s].next[s]
//             i.next[s].next[LinkedList.nextState[s]] = i
//             j.next[LinkedList.nextState[s]] = i.next[s]
            
//             // Frame the rest of the nodes
//             all n: IntNode - (i + j + i.next[s]) | n.next[LinkedList.nextState[s]] = n.next[s]
//           }
//         }
//       }
//     } else {
//       // IF SORTED: Frame the entire state so it doesn't scramble
//       LinkedList.head[LinkedList.nextState[s]] = LinkedList.head[s]
//       all n: IntNode | n.next[LinkedList.nextState[s]] = n.next[s]
//     }
//   }
// }










pred swappingV2 {
  // There may exist some integer which is out of order
  // That integer swaps left in the next state if the node to the left has a value greater than that node
  // Frame condition: The next field of all nodes unaffected by the swap are the same

  // state cannot be FirstState because first state has not inserted the out of order element and thus is sorted

  all s: State - LinkedList.firstState | {  // this could be unsat because saying that no state can be the first state????? or maybe not    
    // i.next[s].value < i.value
    not sorted[s] implies {
      let nx = LinkedList.nextState[s] | {
        some nx
        some i: IntNode | {
          let j = i.next[s] | {
            some j and j.value < i.value

            i.next[nx] = j.next[s]
            j.next[nx] = i
            // a -> c -> b
            // a -> b -> c
            //frame condition
            all n: IntNode - (i + j) | n.next[nx] = n.next[s]
          }
        }
      }
    }
    // if the next node has a smaller value then do the following:

    //next node after i in the next state is the next node of teh
    //swapping nexts with smaller value node in order to switch their position in the list
  }
}



---------------------------------------------------------------

pred someList {
    // some l: LinkedList | wellformed and newInsertionV2 and swapping
    // some l: LinkedList | wellformed and newInsertionV2 //and swappingV3
    wellformed
    newInsertionV2
    swappingForced
}
run {
  someList
 } for exactly 5 IntNode, exactly 6 State, exactly 1 LinkedList for {nextState is linear}


 