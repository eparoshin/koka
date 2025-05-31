module mapreduce

import std/os/env
import std/os/task
import std/num/int32
import std/num/random

fun calcfn(n : int) : pure promise<int>
  task { n }

pub fun main()
  val lst = list(0, 1000)
  val newlst = lst.map(calcfn).await
  show(foldl1(newlst, fn(i, j) if i < j then j else i))
