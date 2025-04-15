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

-- Lexer. `Nat` here is a state variable determining when to skip values (for Func tokens)
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

--TODO: Term tokenizer

def maketokens : String → List Token
  | "" => []
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

def formatString : String → String
  | "" => ""
  | string => String.mk (formatStringLogic string.data)

#eval formatString "(1131)sin(2)"

--  better idea in practice. splits string into lists of component terms,
--  for reconstruction
--  string data → string tokens → token → buffer → output terms
/-  TODO: accommodate functions :(
          reconstruct expression (actually a nontrivial task)
            thus we need an endomorphism
-/
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

#eval stringToTerms "323456 + (4+5) *sin(x)*cos(x)" (.Func)
#eval maketokens "323456 + (4+5) *sin(x)*cos(x)"
#eval flattenTokens (maketokens "323456 + (4+5) *(sin(x)*cos(x))")

/-
  TODO: Complete lexer
    Idea: Take in a string, its tokens, and a list with empty entries of the same length
          as the list of tokens. Then, for each token enum, insert the strings in order
          in the appropriate slot (given by the list of tokens)
-/
def Lexer : String → List Token → List String → List String
  | "", _, _, _ => []
  | string, t::ts, _, _ => _

end Lexer

-- def makeStringFunc : List Char → String
--   | [] => ""
--   | c::c'::c''::_ => (String.mk ([c] ++ [c'] ++[c'']))
--   | _::_ => "!"

-- Split strings into terms
/-  TODO: split this into different functions... one to tokenize a list of chars, then one
    to build a string based on that tokenization

    Better idea: declare functions that output lists of every different kind of term in the sentence,
    parse the entire sentence into these separate lists, then reconstruct it according to a tokenization.
-/

-- def stringToTermsLogic : List Char → Nat → List Char → List String → List String
--   | [], _, [], out => List.reverse out
--   | [], _, st::sts, out => stringToTermsLogic [] 0 [] ([(String.mk (st::sts))] ++ out)
--   | c::cs, 0, [], out =>
--     if c.isDigit then
--       stringToTermsLogic cs 0 [c] out
--     else if checkForFunc (makeStringFunc (c::cs)) then
--       stringToTermsLogic cs 2 [c] out
--     else if c.isAlpha then
--       stringToTermsLogic cs 0 [] ([(String.mk [c])] ++ out)
--     else if c = ' ' then
--       stringToTermsLogic cs 0 [] out
--     else
--       stringToTermsLogic cs 0 [] ([(String.mk [c])] ++ out)
--   | c::cs, 0, st::sts, out =>
--     if c.isDigit then
--       stringToTermsLogic cs 0 (c::st::sts) out
--     else if checkForFunc (makeStringFunc (c::cs)) then
--       stringToTermsLogic cs 2 [c] ((String.mk (st::sts))::out)
--     else if c.isAlpha then
--       stringToTermsLogic cs 0 [] ([(String.mk [c])] ++ (String.mk (st::sts))::out)
--     else if c = ' ' then
--       stringToTermsLogic cs 0 (st::sts) out
--     else
--       stringToTermsLogic cs 0 [] ([(String.mk [c])] ++ (String.mk (st::sts))::out)
--   | c::cs, Nat.succ n, strings, out =>
--     stringToTermsLogic (cs) (n) (strings ++ [c]) out

-- def stringToTerms : String → List String
--   | "" => []
--   | string => stringToTermsLogic string.data 0 [] []

#eval String.mk ("9".data ++ ['2'])
#eval stringToTerms "(sin(x)+a)+(x*22)"

-- TODO: make better string converter (want to accommodate tokens like "sin")

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

#eval shuntingYard (stringToTerms "(33+3)*(x + 3)")

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
