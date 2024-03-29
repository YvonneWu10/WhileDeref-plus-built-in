## 语义理论：证明带 built-in 函数的程序语言精化关系的基本性质

考虑在 WhileDeref 语言中加入 write_int、read_int 这两个 built-in 函数，此时，程序语句的指称语义应当将程序语句产生的 built-in 操作及其结果也纳入考虑。

+ 要求 1：定义新语言的语法与指称语义，定义语义等价与精化关系，证明语义等价是一个等价关系，精化关系是一个Pre-order。
+ 要求 2：证明二元运算、一元运算、解引用、write_int、赋值语句与 if 语句都能保持精化关系。
+ 要求 3：证明 while 循环语句能保持精化关系。
