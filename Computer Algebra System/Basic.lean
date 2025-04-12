-- TODO: Shunting-Yard is unavoidable, but we can definitely do it
namespace ExpressionParsing
#check String
#check List

#eval String.mk ['a', 'b', 'c']
#eval String.data "Hey"
#check Char.isAlphanum

def opPrecedence : String → Int
  | "^" => 3
  | "*" => 2
  | "/" => 2
  | "+" => 1
  | "-" => 1
  | "=" => 0
  | _ => -1

def isOperation (c : String) : Bool :=
  c = "+"
  || c = "-"
  || c = "*"
  || c = "/"
  || c = "^"

def isParentheses (c : String) : Bool :=
  c = "("
  || c = ")"

def isSpace (c : String) : Bool :=
  c = " "

def stringAlphanumHelper : List Char → Bool
  | [] => true
  | c::cs =>
    if !c.isAlphanum then
      false
    else
      -- dbg_trace "{c}"
      stringAlphanumHelper cs

def alphanum : String → Bool
  | "" => false
  | S =>
    stringAlphanumHelper S.data

def Tokenizer : List String → List String
  | [] => []
  | a::as =>
    if alphanum a then
      "n"::Tokenizer as
    else if isOperation a then
      "o"::Tokenizer as
    else if isParentheses a then
      "p"::Tokenizer as
    else if isSpace a then
      Tokenizer as
    else
      "!"::Tokenizer as


def removeWhitespace : List Char → List Char → List Char
  | [], [] => []
  | [], a => a
  | c::cs, ns =>
    if c != ' ' then
      removeWhitespace cs (ns ++ [c])
    else
      removeWhitespace cs ns

#eval stringAlphanumHelper "9".data
#eval (removeWhitespace "(2+3) + (3 + 2)".data [])

-- TODO: make better string converter (want to accommodate tokens like "sin")
#eval Tokenizer ((removeWhitespace "(2+3) + (3 + 2)".data []).map (Char.toString))

def parensCount : List String → Nat
  | [] => 0
  | a::as =>
    if a = "p" then
      1 + parensCount as
    else
      parensCount as

-- Helper method to check whether next term is compatible
-- Can be used by itself to ensure first element in list meets specs
def nextTerm :  List String → String → Bool
  | [], _ => False
  | t::_, c =>
    if t = c then
      True
    else
      False

#check List.head

def getNextTerm : List String → String
  | [] => " "
  | x::_ => x

-- Helper method to check whether there are two neighboring expressions of the same type
def neighborTerm : List String → String → Bool
  | [], _ => False
  | t::ts, c =>
    if t = c ∧ (nextTerm ts c) then
      True
    else
      neighborTerm ts c

-- Verifies whether expression is well-formed, sends error code
-- use except monad
#check Except

def expressionError (l : List String) : String :=
  match l with
  | [] => "This expression is empty"
  | l =>
    if (parensCount l) % 2 = 1 then
      "Expression contains mismatched parentheses."
    else if nextTerm l "o" then
      "Expressions cannot start with operators."
    else if neighborTerm l "o" then
      "Expression contains neighboring operators."
    else if neighborTerm l "n" then
      "Expression contains neighboring numbers."
    else
      "cont"

#check List.all


-- #eval neighborTerm (Tokenizer "(2+3*a)".data) 'o'
-- #eval expressionError (Tokenizer "(2+3*a)".data)
#eval  ([3] ++ [1, 2, 3]).head?

def testFunc2 : List Nat → List Nat
  | [] => []
  | x::xs => 1::x::xs

def testFunc1 : List Nat → List Nat
  | [] => []
  | xs => testFunc2 xs

-- gives us the updated output
def shuntYardOpHelper : String → List String → List String → List String
  | o₂, [], out => o₂::out
  | o₂, o₁::ops, out =>
    if opPrecedence o₂ > opPrecedence o₁ then
      shuntYardOpHelper o₂ (ops) (o₁::out)
    else
      o₂::out

-- drop operations off opstack
-- we could make this polymorphic. would pass condition as argument
def shuntYardOpStackHelper : String → List String → List String
  | _, [] => []
  | o₂, o₁::ops =>
    if opPrecedence o₂ > opPrecedence o₁ then
      shuntYardOpStackHelper o₂ ops
    else
      ops

-- update output after parentheses
def sYParensHelper : String → List String → List String → List String
  | _, [], _ => ["!", "2"]
  | rp, op::ops, out =>
    dbg_trace "{ops}"
    if op != "(" then
      sYParensHelper rp ops (op::out)
    else
      out

-- update opstack after parentheses
def sYParensOpStackHelper : String → List String → List String
  | _, [] => []
  | rp, op::ops =>
    if op != "(" then
      sYParensOpStackHelper rp ops
    else
      ops

#eval sYParensHelper ")" ["*","+","(", "+"] []

/- For Shunting-Yard, the idea is, instead of using stacks, use lists like a::as
and append directly to the head. pop the head as needed.

Notable that there is a kind of separation of concerns with respect to each argument.
Need separate helper functions for manipulating the operator stack vs. the output stack.

TODO: finish parentheses logic
-/
def shuntingYard :
    List String → List String → List String → List String
  | [], [], out => out
  | [], op::_, out => op::out
  | t::ts, ops, out =>
    if alphanum t then
      shuntingYard ts ops (t::out)
    else if isOperation t then
      shuntingYard
        ts (t::shuntYardOpStackHelper t ops) (shuntYardOpHelper t ops out)
    else if t = "(" then
      shuntingYard ts (t::ops) out
    else if t = ")" then
      shuntingYard ts (sYParensOpStackHelper t ops) (sYParensHelper t ops out)
    else
      ["!", "1"]


end ExpressionParsing



namespace Tree
open ExpressionParsing
-- inductive BinaryTree where
--   | leaf : BinaryTree
--   | node : BinaryTree → BinaryTree → BinaryTree
inductive BTree (α : Type) where
  | empty : BTree α
  | node  (val : α) (l : BTree α) (r : BTree α) : BTree α

def exampleTree : BTree Nat :=
  BTree.node 5
    (BTree.node 3
      (BTree.node 3 BTree.empty BTree.empty)
      BTree.empty)
    (BTree.node 7 BTree.empty BTree.empty)

def BinaryTree.repr {α : Type} [ToString α] : BTree α → String
  | .empty => "empty"
  | .node v l r =>
    "(node " ++ toString v ++ " " ++ repr l ++ " " ++ repr r ++ ")"

def traversal {α : Type} [ToString α] : BTree α → String
  | .empty => "empty"
  | .node v left right =>
    traversal left ++ " node: " ++ toString v ++ " " ++ traversal right

def insert {α : Type} : α → BTree α → BTree α
  | a, .empty => .node a (.empty) (.empty)
  | a, .node v (.empty) r =>
    .node v (.node a .empty .empty) r
  | a, .node v l (.empty) =>
    .node v l (.node a .empty .empty)
  | a, .node v l r =>
    .node v l (insert a r)

-- TODO: Parse parentheses
-- transforms an expression into a binary tree
def listToTree : List String → List String → BTree String →  BTree String
  | [], _, tree => tree
  | _, [], tree => tree
  | x::xs, _::ts, .empty =>
    listToTree xs ts (.node x .empty .empty)
  | x::xs, t::ts, .node v l r =>
      if t == "n" then
        if getNextTerm ts == "o" then
          listToTree xs ts (.node x (.node v l r) .empty)
        else
          listToTree xs ts (.node v l (.node x .empty .empty))
      else if t == "o" then
        listToTree xs ts (.node x (.node v l r) .empty)
      else
        .node v l r

-- USEFUL DEBUG COMMANDS
-- dbg_trace "input node: {v}"
-- dbg_trace "Current inputs: {xs}, {ts}, tree: {tree}"

def exampleList := "2+4*5".data
def exampleListTokens := (Tokenizer exampleList)
#eval exampleListTokens
#check listToTree exampleList exampleListTokens .empty
#eval traversal (listToTree exampleList exampleListTokens .empty)

#eval getNextTerm (exampleListTokens.tail.tail.tail)

end Tree
