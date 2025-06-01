module mapreduce

import std/os/env
import std/os/task
import std/num/int32
import std/num/random

fun calcone(n : int) : pure int
  var i := 0;
  var res := 0;
  while { i < n % 67 }
    i := i + 1
    res := res + (n * n + n / 177)
  res


fun calconefn(n : int) : pure promise<int>
  task{ calcone(n) }

fun calc(n : int) : pure int
  val lst = list(0, 1000)
  foldl1(lst.map(calconefn).await, fn(i : int, j : int) if i < j then j else i)

fun calcfn(n : int) : pure promise<int>
  task { calc(n) }

pub fun main()
  val lst = list(0, 100)
  val newlst = lst.map(calcfn).await
  show(foldl1(newlst, fn(i, j) if i < j then j else i))
