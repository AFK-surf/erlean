pub fn identity(value: a) -> a {
  value
}

pub fn pair(left: a, right: b) -> #(a, b) {
  #(left, right)
}

pub fn empty() -> List(a) {
  []
}

pub fn prepend(head: a, tail: List(a)) -> List(a) {
  [head, ..tail]
}
