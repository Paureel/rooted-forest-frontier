import Std
-- Intentional negative control: missing a second hard credit saves only
-- one cut, which cannot pay the C continuation's coefficient at X=128.
example : (16 : Int) * 30 ≤ 2 * 128 + 32 := by decide
