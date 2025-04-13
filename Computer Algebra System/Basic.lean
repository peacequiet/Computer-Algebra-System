-- TODO: Shunting-Yard is unavoidable, but we can definitely do it
namespace ExpressionParsing
#check String
#check List

#eval String.mk ['a', 'b', 'c']
#eval String.data "Hey"
#check Char.isAlphanum

section Tokenizing
def opPrecedence : String → Int
  | "(" => 15
  | ")" => 15
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

def stringAlphaHelper : List Char → Bool
  | [] => true
  | c::cs =>
    if !c.isAlpha then
      false
    else
      -- dbg_trace "{c}"
      stringAlphaHelper cs

def isAlpha : String → Bool
  | "" => false
  | S =>
    stringAlphaHelper S.data

def stringNumHelper : List Char → Bool
  | [] => true
  | c::cs =>
    if !c.isDigit then
      false
    else
      -- dbg_trace "{c}"
      stringNumHelper cs

def isNum : String → Bool
  | "" => false
  | S =>
    stringNumHelper S.data

def isFunc : String → Bool
  | "" => false
  | s =>
    if s.toLower = "sin" then
      true
    else if s.toLower = "cos" then
      true
    else if s.toLower = "tan" then
      true
    else if s.toLower = "exp" then
      true
    else
      false

#eval isNum "2222"

def Tokenizer : List String → List String
  | [] => []
  | a::as =>
    if isFunc a then
      "func"::Tokenizer as
    else if isNum a then
      "n"::Tokenizer as
    else if isAlpha a then
      "v"::Tokenizer as
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

def removeWhitespaceString : List Char → List Char → List Char
  | [], [] => []
  | [], a => a
  | c::cs, ns =>
    if c != ' ' then
      removeWhitespace cs (ns ++ [c])
    else
      removeWhitespace cs ns

-- Split strings into terms
-- TODO: accommodate functions
def stringToTermsLogic : List Char → List Char → List String → List String
  | [], [], out => List.reverse out
  | [], st::sts, out => stringToTermsLogic [] [] ([(String.mk (st::sts))] ++ out)
  | c::cs, [], out =>
    if c.isDigit then
      stringToTermsLogic cs [c] out
    else if c.isAlpha then
      stringToTermsLogic cs [] ([(String.mk [c])] ++ out)
    else if c = ' ' then
      stringToTermsLogic cs [] out
    else
      stringToTermsLogic cs [] ([(String.mk [c])] ++ out)
  | c::cs, st::sts, out =>
    if c.isDigit then
      stringToTermsLogic cs (c::st::sts) out
    else if c.isAlpha then
      stringToTermsLogic cs [] ([(String.mk [c])] ++ (String.mk (st::sts))::out)
    else if c = ' ' then
      stringToTermsLogic cs (st::sts) out
    else
      stringToTermsLogic cs [] ([(String.mk [c])] ++ (String.mk (st::sts))::out)

def stringToTerms : String → List String
  | "" => []
  | string => stringToTermsLogic string.data [] []

#eval String.mk ("9".data ++ ['2'])
#eval stringToTerms "(22222+a)+(x+22)"
#eval (removeWhitespace "(2+3) + (3 + 2)".data [])
#eval (removeWhitespace "(2+3) + (3 + 2)".data []).map (Char.toString)

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

end Tokenizing

section ShuntingYard
-- gives us the updated output
def shuntYardOpHelper : String → List String → List String → List String
  | o₁, [], out => out
  | o₁, o₂::ops, out =>
    if opPrecedence o₂ > opPrecedence o₁ && o₂ != "(" then
      shuntYardOpHelper o₁ (ops) (o₂::out)
    else
      out

-- drop operations off opstack
-- we could make this polymorphic. would pass condition as argument
def shuntYardOpStackHelper : String → List String → List String
  | _, [] => []
  | o₁, o₂::ops =>
    if opPrecedence o₂ > opPrecedence o₁ && o₂ != "(" then
      shuntYardOpStackHelper o₁ ops
    else if opPrecedence o₂ > opPrecedence o₁ && o₂ = "(" then
      o₂::ops
    else
      ops

-- update output after parentheses
def sYParensHelper : String → List String → List String → List String
  | _, [], out => out
  | rp, op::ops, out =>
    -- dbg_trace "{ops}"
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
      -- dbg_trace "{op}"
      -- dbg_trace "{ops}"
      ops

#eval sYParensOpStackHelper ")" ["*","+","(", "+"]

/- For Shunting-Yard, the idea is, instead of using stacks, use lists like a::as
and append directly to the head. pop the head as needed.

Notable that there is a kind of separation of concerns with respect to each argument.
Need separate helper functions for manipulating the operator stack vs. the output stack.

useful debug:
  dbg_trace "{t::ts}, {ops}, {out}"

Outputs a reverse-postfix expression. Should create a wrapper for second reversal.
-/

def shuntingYardLogic :
    List String → List String → List String → List String
  | [], [], out => List.reverse out
  | [], op::ops, out => shuntingYardLogic [] ops (op::out)
  | t::ts, ops, out =>
    if isNum t then
      shuntingYardLogic ts ops (t::out)
    else if isAlpha t then
      shuntingYardLogic ts ops (t::out)
    else if isOperation t then
      shuntingYardLogic
        ts (t::shuntYardOpStackHelper t ops) (shuntYardOpHelper t ops out)
    else if t = "(" then
      shuntingYardLogic ts (t::ops) out
    else if t = ")" then
      shuntingYardLogic ts (sYParensOpStackHelper t ops) (sYParensHelper t ops out)
    else
      ["!", "1"]

  def shuntingYard : List String → List String
  | [] => []
  | strings => shuntingYardLogic strings [] []

#eval shuntingYard ((removeWhitespace "(3+3)*(2 + 3)".data []).map (Char.toString))

#eval shuntingYard (stringToTermsLogic "(33+3)*(x + 3)".data [] [])

#eval '('.isAlphanum
end ShuntingYard
end ExpressionParsing


/- TODO: Rewrite the entire listToTree sequence to accommodate postfix expressions instead of infix
-/
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

def exampleList := stringToTerms "a+4*5"
def exampleListTokens := (Tokenizer exampleList)
#eval exampleListTokens
#check listToTree exampleList exampleListTokens .empty
#eval traversal (listToTree exampleList exampleListTokens .empty)

#eval getNextTerm (exampleListTokens.tail.tail.tail)

end Tree
