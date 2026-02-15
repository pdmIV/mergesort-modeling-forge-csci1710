#lang forge/froglet

sig IntArray {
    elements: pfunc Int -> Int,
    lastIndex: one Int
}

sig MergeState {
    arr: one IntArray // should become more sorted over time (assume ascending order is sorted)
}