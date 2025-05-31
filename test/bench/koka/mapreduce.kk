module mapreduce

import std/os/env
import std/os/task
import std/num/int32
import std/num/random

fun calc(n : int) : pure int
  var i := 0;
  var res := 0;
  while {i < n % 67}
    i := i + 1
    res := res + (n * n + n / 177)
  res

fun calcfn(n : int) : pure promise<int>
  task { calc(n) }

pub fun main()
  val lst = list(0, 10000000)
  val newlst = lst.map(calcfn).await
  show(foldl1(newlst, fn(i, j) if i < j then j else i))
