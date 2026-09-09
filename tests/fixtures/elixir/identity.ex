defmodule ErleanIdentity do
  def identity(value), do: value
  def pair(left, right), do: {left, right}
  def empty(), do: []
  def prepend(head, tail), do: [head | tail]
end
