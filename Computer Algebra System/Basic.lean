-- TODO: Shunting-Yard is unavoidable, but we can definitely do it
import Lean.Expr
import Lean.ToExpr

namespace ExpressionParsing
open Lean
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

def isOperationChar (c : Char) : Bool :=
  c = '+'
  || c = '-'
  || c = '*'
  || c = '/'
  || c = '^'

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

def checkForFunc : String → Bool
  | "sin" => true
  | "cos" => true
  | "tan" => true
  | "exp" => true
  | _ => false

#eval isNum "2222"

inductive Token
  | Num
  | Var
  | Op
  | Parens
  | Func
  deriving Repr, BEq

#check DecidableEq

def tokenToNat : Token → Nat
  | .Num => 0
  | .Var => 1
  | .Op => 3
  | .Parens => 4
  | .Func => 5

def Token.toString : Token → String
  | Num    => "Num"
  | Var    => "Var"
  | Op     => "Op"
  | Parens => "Parens"
  | Func   => "Func"

instance : ToString Token where
  toString
    | .Num    => "Num"
    | .Var    => "Var"
    | .Op     => "Op"
    | .Parens => "Parens"
    | .Func   => "Func"


instance : Repr Token where
  reprPrec t _ := t.toString
section Lexer
def isFuncToken : List Char → Bool
  | [] => false
  | c::c'::c''::_ =>
    if (String.mk [c, c', c'']).toLower = "sin" then
      true
    else if (String.mk [c, c', c'']).toLower = "cos" then
      true
    else if (String.mk [c, c', c'']).toLower = "tan" then
      true
    else if (String.mk [c, c', c'']).toLower = "exp" then
      true
    else
      false
  | _ =>
    false

def isOpToken (c : Char) : Bool :=
  c = '+'
  || c = '-'
  || c = '*'
  || c = '/'
  || c = '^'

-- pre-lexer. `Nat` here is a state variable determining when to skip values (for Func tokens)
-- gets a char-by-char tokenization of a list of chars
def makeTokensLogic : List Char → Nat → List Token
  | [], _ => []
  | _::as, Nat.succ n =>
    makeTokensLogic as n
  | a::as, 0 =>
    if isFuncToken (a::as) then
      .Func::.Func::.Func::makeTokensLogic as 2
    else if a.isDigit then
      .Num::makeTokensLogic as 0
    else if a.isAlpha then
      .Var::makeTokensLogic as 0
    else if isOpToken a then
      .Op::makeTokensLogic as 0
    else if a = '(' || a = ')' then
      .Parens::makeTokensLogic as 0
    else
      makeTokensLogic as 0

-- TODO: check whether neighboring characters are valid/syntactic validity of string
-- TODO: auto-insert multiplication
-- And maybe some proofs about the kinds of values that are allowed in?

def maketokens : String → List Token
  | string => makeTokensLogic (string.data) 0

#eval maketokens "2+sin(x)"

def formatStringLogic : List Char → List Char
  | [] => []
  | c::cs =>
    if c.isAlphanum then
      c::formatStringLogic cs
    else if c = '(' || c = ')' then
      c::formatStringLogic cs
    else if isOperationChar c then
      c::formatStringLogic cs
    else
      formatStringLogic cs

-- filters out all invalid characters before transforming string into terms
def formatString : String → String
  | string => String.mk (formatStringLogic string.data)

#eval formatString "(1131)sin(2)"

--  splits string into lists of component terms,
--  string data → string tokens → token → buffer → output terms
def stringToTermsLogic : List Char → List Token → Token → List Char → List String
  | [], _, _, [] => []
  | [], tokens, t, b::bs =>
    (String.mk (b::bs).reverse)::stringToTermsLogic [] tokens t []
  | _::_, [], t, buff =>
    (String.mk (buff).reverse)::stringToTermsLogic [] [] t []
  | ch::chs, to::tos, t, [] =>
    if to == t then
      stringToTermsLogic chs tos t [ch]
    else
      stringToTermsLogic chs (tos) t []
  | ch::chs, to::tos, t, b::bs =>
    if to == t then
      stringToTermsLogic chs tos t (ch::(b::bs))
    else
      (String.mk (b::bs).reverse)::stringToTermsLogic chs (tos) t []

-- transforms a string into constituent terms
def stringToTerms : String → Token → List String
  | string, t => stringToTermsLogic (formatString string).data (maketokens string) t []

-- Flattens tokens using a buffer, in a similar manner to stringTerms above
def flattenTokensLogic : List Token → List Token →  List Token
  | [], []=> []
  | [], t::_ => t::flattenTokensLogic [] []
  | t₁::ts, [] =>
      flattenTokensLogic ts [t₁]
  | t₁::ts, t₂::_ =>
    if t₁ == t₂ && t₁ != .Parens then
      flattenTokensLogic ts [t₁]
    else
      t₂::flattenTokensLogic ts [t₁]
  termination_by args1 args2 => (args1.length, args2.length)

def flattenTokens : List Token → List Token
  | tokens => flattenTokensLogic tokens []

def createFlatTokens : String → List Token
  | string => flattenTokens (maketokens string)

#eval stringToTerms "323456 + (4+5) *sin(x)*cos(x)" (.Func)
#eval createFlatTokens "323456 + (4+5) *(sin(x)*cos(x))"
#eval flattenTokens (maketokens "323456 + (4+5) *(sin(x)*cos(x))")

#check ToExpr Nat

-- stores a record of all valid terms in string
structure lexerEnv where
  nums : List String
  vars : List String
  ops : List String
  parens : List String
  funcs : List String
  deriving Repr

def lexerEnv.create : String → lexerEnv
  | string => { nums := stringToTerms string (.Num)
                vars := stringToTerms string (.Var)
                ops := stringToTerms string (.Op)
                parens := stringToTerms string (.Parens)
                funcs := stringToTerms string (.Func) }

#eval lexerEnv.create "323456 + (4+5) *sin(x)*cos(x)"

def lexerLogic : List Token → lexerEnv → List String
  | [], _ => []
  | t::ts, env =>
    match t with
    | .Num =>
      match env.nums with
      | [] => []
      | num::nums' => num::lexerLogic ts {env with nums := nums'}
    | .Var =>
      match env.vars with
      | [] => []
      | var::vars' => var::lexerLogic ts {env with vars := vars'}
    | .Op =>
      match env.ops with
      | [] => []
      | op::ops' => op::lexerLogic ts {env with ops := ops'}
    | .Parens =>
      match env.parens with
      | [] => []
      | p::parens' => p::lexerLogic ts {env with parens := parens'}
    | .Func =>
      match env.funcs with
      | [] => []
      | func::funcs' => func::lexerLogic ts {env with funcs := funcs'}

/-
  TODO: Complete lexer -- COMPLETE
    Idea: Take in a string, its tokens, and a list with empty entries of the same length
          as the list of tokens. Then, for each token enum, insert the strings in order
          in the appropriate slot (given by the list of tokens)
    Post-mortem: We used a structure to ensure the type signature did not get too cluttered.
                  But because the operation is repeated, I'm left wondering if there is a
                  more elegant way to do this.
-/
-- reconstructs valid expression out of terms

def lexer : String → List String
  | string =>
    lexerLogic (createFlatTokens string) (.create string)

#eval lexerLogic (flattenTokens (maketokens "323456 + (4+5) *sin(x)*cos(x)")) (lexerEnv.create "323456 + (4+5) *sin(x)*cos(x)")
#eval (flattenTokens (maketokens "323456 + (4+5) *sin(x)*cos(x)"))
#eval lexer "sin(x + 2)*cos(x + 9)/2"

end Lexer

#eval String.mk ("9".data ++ ['2'])
#eval stringToTerms "(sin(x)+a)+(x*22)"

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
-- use except monad?
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

#eval shuntingYard (lexer "(33+3)*(x + 3)*(0)*sin(34)")

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

def exampleList := stringToTerms "sin(x)+4*5"
def exampleListTokens := (Tokenizer exampleList)
#eval exampleListTokens
#check listToTree exampleList exampleListTokens .empty
#eval traversal (listToTree exampleList exampleListTokens .empty)

#eval getNextTerm (exampleListTokens.tail.tail.tail)

end Tree
