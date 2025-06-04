module mapreduce

import std/os/env
import std/os/task
import std/num/int32
import std/num/random

fun calcone(n : int) : pure promise<int>
  task { n * n }


fun calconefn(n : int) : pure promise<int>
  task{ calcone(n) }.join

fun calc(n : int) : pure promise<int>
  list(0, 10000).map(calconefn).wait_all.transform(fn(l) foldl1(l, fn(i : int, j : int) if i < j then j else i))


pub fun main()
  val lst = list(0, 1000)
  val result = lst.map(calc).wait_all.transform(fn(l) foldl1(l, fn(i, j) if i < j then j else i)).await
  show(result)
