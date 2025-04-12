-- TODO: Shunting-Yard is unavoidable, but we can definitely do it
namespace ExpressionParsing
#check String
#check List

#eval String.mk ['a', 'b', 'c']
#eval String.data "Hey"
#check Char.isAlphanum

def opPrecedence : Char → Int
  | '^' => 3
  | '*' => 2
  | '/' => 2
  | '+' => 1
  | '-' => 1
  | '=' => 0
  | _ => -1

def isOperation (c : Char) : Bool :=
  c = '+'
  || c = '-'
  || c = '*'
  || c = '/'
  || c = '^'

def isParentheses (c : Char) : Bool :=
  c = '('
  || c = ')'

def isSpace (c : Char) : Bool :=
  c = ' '

#eval String.al

def stringAlphanumHelper : List Char → Bool
  | [] => false
  | c::cs =>
    if c.isAlphanum = false then
      false
    else
      stringAlphanumHelper cs

def String.isAlphanum : String → Bool
  | "" => false
  | S => stringAlphanumHelper S.data

def Tokenizer : List Char → List Char
  | [] => []
  | a::as =>
    if a.isAlphanum then
      'n'::Tokenizer as
    else if isOperation a then
      'o'::Tokenizer as
    else if isParentheses a then
      'p'::Tokenizer as
    else if isSpace a then
      Tokenizer as
    else
      '!'::Tokenizer as

#eval Tokenizer "(2+3) + (3 + 2)".data

def parensCount : List Char → Nat
  | [] => 0
  | a::as =>
    if a = 'p' then
      1 + parensCount as
    else
      parensCount as

-- Helper method to check whether next term is compatible
-- Can be used by itself to ensure first element in list meets specs
def nextTerm :  List Char → Char → Bool
  | [], _ => False
  | t::_, c =>
    if t = c then
      True
    else
      False

#check List.head

def getNextTerm : List Char → Char
  | [] => ' '
  | x::_ => x

-- Helper method to check whether there are two neighboring expressions of the same type
def neighborTerm : List Char → Char → Bool
  | [], _ => False
  | t::ts, c =>
    if t = c ∧ (nextTerm ts c) then
      True
    else
      neighborTerm ts c

-- Verifies whether expression is well-formed, sends error code
-- use except monad
#check Except

def expressionError (l : List Char) : String :=
  match l with
  | [] => "This expression is empty"
  | l =>
    if (parensCount l) % 2 = 1 then
      "Expression contains mismatched parentheses."
    else if nextTerm l 'o' then
      "Expressions cannot start with operators."
    else if neighborTerm l 'o' then
      "Expression contains neighboring operators."
    else if neighborTerm l 'n' then
      "Expression contains neighboring numbers."
    else
      "cont"

#check List.all


#eval neighborTerm (Tokenizer "(2+3*a)".data) 'o'
#eval expressionError (Tokenizer "(2+3*a)".data)
#eval  ([3] ++ [1, 2, 3]).head?

def testFunc2 : List Nat → List Nat
  | [] => []
  | x::xs => 1::x::xs

def testFunc1 : List Nat → List Nat
  | [] => []
  | xs => testFunc2 xs

def shuntYardOpHelper
    (t : Char) (opStack : List Char) (out : List Char) : List Char
  | t, [], _ => t::_
  | t, op, _ =>


def shuntingYard
    (tokens : List Char) (opStack : List Char) (out : List Char) : List Char
  | [], _, o => _
  | t::ts, op, o =>
    if Tokenizer t = "n" then
      shuntingYard tokens opStack (t::out)
    else if Tokenizer t = "o" then


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
def listToTree : List Char → List Char → BTree Char →  BTree Char
  | [], _, tree => tree
  | _, [], tree => tree
  | x::xs, _::ts, .empty =>
    listToTree xs ts (.node x .empty .empty)
  | x::xs, t::ts, .node v l r =>
      if t == 'n' then
        if getNextTerm ts == 'o' then
          listToTree xs ts (.node x (.node v l r) .empty)
        else
          listToTree xs ts (.node v l (.node x .empty .empty))
      else if t == 'o' then
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
