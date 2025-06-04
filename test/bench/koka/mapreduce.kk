module mapreduce

import std/os/env
import std/os/task
import std/num/int32
import std/num/random

fun calcone(n : int) : pure promise<int>
  task { n * n }


fun calconefn(n : int) : pure promise<int>
  task{ calcone(n) }.join

fun calc(num: int, n : int) : pure promise<int>
  list(0, num).map(calconefn).wait_all.transform(fn(l) foldl1(l, fn(i : int, j : int) if i < j then j else i))


pub fun main()
  val args = get-args()
  val outer_n = args.head.default("").parse-int.default(0)
  val inner_n = args.tail.head.default("").parse-int.default(0)
  val lst = list(0, outer_n)
  val result = lst.map(fn(n) calc(inner_n, n)).wait_all.transform(fn(l) foldl1(l, fn(i, j) if i < j then j else i)).await
  show(result)
