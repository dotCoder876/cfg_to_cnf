import Data.Char
import Data.Map (Map)
-- import qualified Data.Map as Map

type Symbol = String
data Rule = Rule Symbol [Symbol]
data Grammar = Grammar [Rule] Symbol

upper :: String -> String
upper s = map toUpper s

lower :: String -> String
lower s = map toLower s

isUppered :: String -> Bool
isUppered s = all isUpper s

isLowered :: String -> Bool
isLowered s = s == lower s

lowered :: [Symbol] -> [Symbol]
lowered xs = filter isLowered xs

uppered :: [Symbol] -> [Symbol]
uppered xs = filter isLowered xs

index :: Eq a => a -> [a] -> Int
index a [] = -1
index a (x:xs) 
  | a == x               = 0
  | a `notElem` (x : xs) = -1
  | otherwise            = 1 + index a xs
  
flatMap :: (a -> [b]) -> [a] -> [b]
flatMap f [] = []
flatMap f (x:xs) = f x ++ flatMap f xs

pretty :: Rule -> String
pretty (Rule statement expression) = statement ++ (" -> " ++ (nice expression))
  where
    nice :: [Symbol] -> String
    nice xs
      | null xs = "/"
      | otherwise = unwords xs

shiny :: Grammar -> String
shiny (Grammar rs s) = unlines (("start symbol: " ++ s):(map show rs))

unique :: Eq a => [a] -> [a]
unique [] = []
unique (x:xs) 
  | elem x xs  = unique xs
  | otherwise = x : unique xs

instance Show Rule where
  show = pretty

instance Show Grammar where
  show = shiny

equivalent :: Rule -> Rule -> Bool
equivalent (Rule s e) (Rule s' e') = (s == s') && (e == e') 

instance Eq Rule where
  x == y = x `equivalent` y

identical :: Grammar -> Grammar -> Bool
identical (Grammar rs s) (Grammar rs' s') = rs' == rs' && s == s'

instance Eq Grammar where
  x == y = x `identical` y

rules :: Grammar -> [Rule]
rules (Grammar rs _) = rs

startingSymbol :: Grammar -> [Rule]
startingSymbol (Grammar rs _) = rs

grammar1 :: Grammar
grammar1 = Grammar [Rule "S" []] "S"

grammar2 :: Grammar
grammar2 = Grammar [Rule "S" ["C", "B", "C"], Rule "B" [], Rule "C" []] "S"

grammar3 :: Grammar
grammar3 = Grammar [Rule "S" ["C", "b", "C"], Rule "B" []] "S"

grammar4 :: Grammar
grammar4 = Grammar [Rule "S" ["C", "b", "C"], Rule "A" ["B"]] "S"

example1 :: Grammar
example1 = Grammar [Rule "S0" ["A", "b", "B"], Rule "S0" ["C"], Rule "B" ["A", "A"], Rule "B" ["A", "C"], Rule "C" ["b"], Rule "C" ["c"], Rule "A" ["a"], Rule "A" []] "S0"

example2 :: Grammar
example2 = Grammar [ Rule "S" ["A", "S", "A"], Rule "S" ["a", "B"],  Rule "A" ["B"],  Rule "A" ["S"],  Rule "B" ["b"],  Rule "B" []]  "S"

variables :: [Symbol]
variables = map (:[]) ['a'..'z'] ++ [ x : show i | i <- [1..] , x <- ['a'..'z'] ]

merge :: Eq a => [a] -> [a] -> [a]
merge xs ys = unique (xs ++ ys)

mergeAll :: Ord a => [[a]] -> [a]
mergeAll xs = foldr merge [] xs

used :: Grammar -> [Symbol]
used (Grammar rs s) =  merge [s] (unique (allSymbols rs))

symbols :: Rule -> [Symbol]
symbols (Rule statement expression) = merge [statement] (unique expression)

allSymbols :: [Rule] -> [Symbol]
allSymbols rs = flatMap symbols rs

contained :: Eq a => [a] -> [a] -> Bool
contained subset superset = filter (`notElem` superset) subset == []

equalCollections :: Eq a => [a] -> [a] -> Bool
equalCollections x y = contained x y && contained y x

difference :: Eq a => [a] -> [a] -> [a]
difference first second = filter (`notElem` second) first

filterVariables :: [Symbol] -> [Symbol] -> [Symbol]
filterVariables xs [] = xs
filterVariables xs (y:ys) = filter (/=y) (filterVariables xs ys)

fresh :: [Symbol] -> Symbol
fresh = head . filterVariables variables

statement :: Rule -> Symbol
statement (Rule statement _) = statement

expression :: Rule -> [Symbol]
expression (Rule _ expression) = expression

--------------------------------------------------------------------------------------------------

start :: Grammar -> Grammar
start (Grammar rs s) = Grammar ((Rule t [s]) : rs) t
  where
    t :: Symbol
    t = upper (fresh (used (Grammar rs s)))

--------------------------------------------------------------------------------------------------

zipToTerm :: [(Symbol, Symbol)] -> [Rule]
zipToTerm xs = map (\x -> (Rule (snd x) [fst x])) xs

substitute :: [(Symbol, Symbol)] -> [Symbol] -> [Symbol]
substitute subs [] = []
substitute subs (s:expression)
  | (notElem s (map fst subs)) = s : (substitute subs expression)
  | otherwise = ((map snd subs) !! (index s (map fst subs))) : (substitute subs expression)
  
substituteRule :: [(Symbol, Symbol)] -> Rule -> Rule
substituteRule subs (Rule statement expression) = Rule statement (substitute subs expression)

substituteAll :: [(Symbol, Symbol)] -> [Rule] -> [Rule]
substituteAll subs rs = zipToTerm subs ++ (map (substituteRule subs) rs)

termSubstitutions :: Grammar -> [Symbol] -> [(Symbol, Symbol)]
termSubstitutions (Grammar rs s) vars = zip (lowered (used (Grammar rs s))) (map upper (filterVariables vars (used (Grammar rs s))))

terminals :: Grammar -> Grammar
terminals (Grammar rs s) = Grammar (substituteAll (termSubstitutions (Grammar rs s) variables) rs) s

--------------------------------------------------------------------------------------------------

eliminate :: [Symbol] -> [Rule] -> [Rule]
eliminate xs [] = []
eliminate xs ((Rule statement []):rs) = (Rule statement []):(eliminate xs rs)
eliminate xs ((Rule statement [s]):rs) = (Rule statement [s]):(eliminate xs rs)
eliminate xs ((Rule statement [s, s']):rs) = (Rule statement [s, s']) : (eliminate xs rs)
eliminate xs ((Rule statement expression):rs) = (flatten xs (Rule statement expression)) ++ (eliminate (drop ((length expression) - 2) xs) rs)

flatten :: [Symbol] -> Rule -> [Rule]
flatten xs (Rule statement []) = [Rule statement []]
flatten xs (Rule statement [s]) = [Rule statement [s]]
flatten xs (Rule statement [s, s']) = [Rule statement [s, s']]
flatten xs (Rule statement (s:expression)) = (Rule statement [s, head xs]) : (flatten (tail xs) (Rule (head xs) expression))

binary :: Grammar -> Grammar
binary (Grammar rs s) = Grammar (eliminate (map upper (filterVariables variables (used (Grammar rs s)))) rs) s

--------------------------------------------------------------------------------------------------

empty :: Rule -> Bool
empty (Rule _ expression) = null expression

allEmpty :: [Rule] -> [Rule]
allEmpty rs = filter empty rs

hasStatement :: Symbol -> Rule -> Bool
hasStatement s (Rule statement _) = s == statement 

withStatement :: Symbol -> [Rule] -> [Rule]
withStatement s rs = filter (hasStatement s) rs

withStatements :: [Symbol] -> [Rule] -> [Rule]
withStatements ss rs = flatMap (`withStatement` rs) ss

statements :: [Rule] -> [Symbol]
statements rs = unique (map statement rs)

expand :: [Rule] -> [Symbol] -> [Symbol] -> [Symbol]
expand rs prev current 
  | prev == current =  current
  | otherwise = expand rs current (merge current (statements (filter  (\r -> (contained (expression r) current)) rs)))

nullable :: [Rule] -> [Symbol]
nullable rs = expand rs [] (unique (statements (allEmpty rs)))

removeNullables :: [Symbol] -> Rule -> [Rule]
removeNullables nulls (Rule statement expression)
  | elem statement nulls = []
  | otherwise = [Rule statement (filter (`notElem` nulls) expression)]

allVersions :: [Symbol] -> [Symbol] -> [[Symbol]]
allVersions = allVersionsHelper [[]]

allVersionsHelper :: [[Symbol]] -> [Symbol] -> [Symbol] -> [[Symbol]]
allVersionsHelper soFar nulls [] = soFar
allVersionsHelper soFar nulls (e:expression)
  | elem e nulls = allVersionsHelper ((map (++ [e]) soFar) ++ soFar) nulls expression
  | otherwise = allVersionsHelper (map (++ [e]) soFar) nulls expression

partialRemoveNullables :: [Symbol] -> Rule -> [Rule]
partialRemoveNullables nulls (Rule statement expression) = map (Rule statement) (allVersions nulls expression)

allRemoveNullables :: Symbol -> [Symbol] -> [Rule] -> [Rule]
allRemoveNullables s nulls rs = unique (filter (\r -> ((statement r == s) || (length (expression r) > 0))) (flatMap (partialRemoveNullables nulls) rs))

removeAllNullables :: Symbol -> [Rule] -> [Rule]
removeAllNullables s rs = allRemoveNullables s (nullable rs) rs

delete :: Grammar -> Grammar
delete (Grammar rs s) = Grammar (removeAllNullables s rs) s

--------------------------------------------------------------------------------------------------

findUnits :: [Rule] -> [(Symbol, Symbol)]
findUnits [] = []
findUnits ((Rule statement [s]):rs) = (statement, s) : (findUnits rs)
findUnits ((Rule statement expression):rs) = findUnits rs

substitute' :: [(Symbol, Symbol)] -> [Symbol] -> [Symbol]
substitute' substitutions [] = []
substitute' substitutions (s:expression)
  | (notElem s (map fst substitutions)) = s : (substitute' substitutions expression)
  | otherwise = ((map snd substitutions) !! (index s (map fst substitutions))) : (substitute' substitutions expression)

substituteRule' :: [(Symbol, Symbol)] -> Rule -> Rule
substituteRule' subs (Rule statement expression) = Rule statement (substitute' subs expression)

substituteAll' :: [(Symbol, Symbol)] -> [Rule] -> [Rule]
substituteAll' subs rs = zipToTerm subs ++ (map (substituteRule' subs) rs)

applyUnits :: [Rule] -> [Rule]
applyUnits rs = substituteAll' unitSubstitutions rs
  where
    foundUnits :: [(Symbol, Symbol)]
    foundUnits = findUnits rs
    unitSubstitutions :: [(Symbol, Symbol)]
    unitSubstitutions = filter ((`notElem` (map snd foundUnits)) . fst) foundUnits

units :: Grammar -> Grammar
units (Grammar rs s) = Grammar (applyUnits rs) s

--------------------------------------------------------------------------------------------------

toCNF :: Grammar -> Grammar
toCNF = units . delete . binary . terminals . start

--------------------------------------------------------------------------------------------------