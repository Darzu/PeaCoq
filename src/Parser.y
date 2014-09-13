{
{-# LANGUAGE DeriveGeneric, DeriveDataTypeable #-}

module Parser where

import Data.Aeson
import Control.Monad
import Data.Char (isSpace, isAlpha, isDigit)
import Data.Typeable
import GHC.Generics

import Lexer
}

%name unsafeParseTerm       Term
%name unsafeParseHypothesis Hypothesis
%tokentype { Token }
%error { parseError }

%token

var { TokSym $$ }
num { TokNum $$ }
'(' { TokLParen }
')' { TokRParen }
'→' { TokArrow }
'∀' { TokForall }
'λ' { TokLambda }
':' { TokColon }
'=' { TokEq }
'_' { TokUnderscore }
',' { TokComma }
'+' { TokPlus }
'-' { TokMinus }
'*' { TokStar }
'%' { TokPercent }
"&&" { TokAndB }
"||" { TokOrB }
":=" { TokColonEq }
"match" { TokMatch }
"as" { TokAs }
"in" { TokIn }
"return" { TokReturn }
"with" { TokWith }
"let" { TokLet }

-- low precedence
%right '→'
%nonassoc '='
%left "&&" "||"
%left '+' '-'
%left '*'
%left APP
%nonassoc '(' ')'
-- high precedence

%%

Term :: { Term }
: var                  { Var $1 }
| num                  { Var $1 }
| '∀' Binders ',' Term { Forall $2 $4 }
| 'λ' Binders ',' Term { Lambda $2 $4 }
| Term '→' Term        { Arrow $1 $3 }
| Term '=' Term        { App (App (Var "eq")    $1) $3 }
| Term '+' Term        { App (App (Var "plus")  $1) $3 }
| Term '-' Term        { App (App (Var "minus") $1) $3 }
| Term '*' Term        { App (App (Var "mult")  $1) $3 }
| Term "&&" Term       { App (App (Var "andb")  $1) $3 }
| Term "||" Term       { App (App (Var "orb")   $1) $3 }
| Term '%' var         { $1 }
| Term Term %prec APP  { App $1 $2 }
| '(' Term ')'         { $2 }

Binders :: { [Binder] }
: Names ':' Term  { [MkBinder $1 (Just $3)] }
| BindersPlus     { $1 }

Binder :: { Binder }
: Names                  { MkBinder $1 Nothing   }
| '(' Names ':' Term ')' { MkBinder $2 (Just $4) }

BindersPlus :: { [Binder] }
: Binder BindersStar { $1 : $2 }

BindersStar :: { [Binder] }
: {- empty -}  { [] }
| BindersPlus  { $1 }

Names :: { [Maybe String] }
: Name       { [$1] }
| Name Names { $1 : $2 }

Name :: { Maybe String }
: var { Just $1 }
| '_' { Nothing }

Hypothesis :: { Hypothesis }
: var ':' Term { MkHyp $1 $3 }

{

instance ToJSON Binder where
instance ToJSON Term where

parseError :: [Token] -> a
parseError l = error $ "Parse error on: " ++ show l

data Term
  = Var String
  | Forall Binders Term
  | Lambda Binders Term
  | Arrow Term Term
  | App Term Term
  deriving (Eq, Generic, Show)

type Type = Term

type Binders = [Binder]

data Binder = MkBinder [Maybe String] (Maybe Type)
  deriving (Eq, Generic, Show)

data Hypothesis
  = MkHyp
  { hName :: String
  , hType :: Term
  }
  deriving (Eq, Generic, Show)

instance ToJSON Hypothesis where

parseTerm :: String -> Term
parseTerm = unsafeParseTerm . scanTokens

parseHypothesis :: String -> Hypothesis
parseHypothesis = unsafeParseHypothesis . scanTokens

}