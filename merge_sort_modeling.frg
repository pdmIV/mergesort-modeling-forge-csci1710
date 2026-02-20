#lang forge/froglet

sig IntArray {
    elements: pfunc Int -> Int,
    lastIndex: one Int
}

pred validArray[a: IntArray] {
  -- Domain is exactly { i | 0 <= i <= lastIndex } (or empty if lastIndex = -1)
  all i: Int | (some a.elements[i]) <=> (0 <= i and i <= a.lastIndex)

  -- lastIndex is either -1 or a nonnegative index
  a.lastIndex = -1 or 0 <= a.lastIndex
}

fun firstIndex[a: IntArray]: one Int {
  a.lastIndex < 0 => -1 else 0
}

pred sorted[a: IntArray] {
  all i: Int | (1 <= i and i <= a.lastIndex) implies
    a.elements[i] >= a.elements[subtract[i, 1]]
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