// a generator effect with one operation
effect yield<a>
  ctl yield( x : a ) : ()

fun traverse( from : int, to : int ) : <div,yield<int>> ()
  if from < to then
    yield(from)
    yield(from * 2)
    traverse(from + 1, to)

// bind the yield operation dynamically
pub fun main() : _e ()
  with ctl yield( i : int)
      println("yielded " ++ i.show)
      if i != 5 then resume(()) else ()
  traverse(0, 10)
  println("done")

