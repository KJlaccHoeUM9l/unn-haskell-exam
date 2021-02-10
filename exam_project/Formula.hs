-- Алексей Гладышев
-- wotpricol@mail.ru

module Formula where

import Data.List
import BooleanSyntax
  (Op(T, F, Neg, And, Or, If, Iff, Xor, Nand, Nor), AssocType(FA, LA, RA, NA),
   Domain, arity, prec, noOp, opText, varName, assoc, evalOp)

-- Ограничения на импорт описаны в лекции 3.  Этот модуль предназначен
-- для работы с функциями любой сигнатуры, то есть с любым набором
-- связок, а не только булевыми формулами. Это достигается тем, что из
-- модуля BooleanSyntax импортируется сам тип Op, но не его
-- конструкторы T, F, Neg, And и т.д. Чтобы импортировались также
-- конструкторы Op, нужно добавить их в скобках после типа, как в
-- случае AssocType, или убрать ограничение на импорт вообще.

-- Пока ограничения временно закомментированны, но поскольку этот
-- модуль предназначен для формул любой сигнатуры, его функции должны
-- работать с ограничениями на импорт из BooleanSyntax, то есть когда
-- ограничния раскомментированны.

type Var = Int

-- C означает "compound", т.е. "составная"
data Formula = V Var | C Op [Formula] -- deriving Show

-- Примеры формул ниже принимаются интерпретатором, если не
-- ограничивать импорт из модуля BooleanSyntax. Однако определения
-- form1 и form2 работают в командной строке.

-- form1 = x v y -> ~z
form1 :: Formula
form1 = C If [C Or [V 0, V 1], C Neg [V 2]]

-- form2 = xy + ~z <-> x v z
form2 :: Formula
form2 = C Iff [C Xor [C And [V 0, V 1], C Neg [V 2]], C Or [V 0, V 2]]

-- form3 = x -> 1
form3 :: Formula
form3 = C If [V 0, C T []]

-- form4 = (x -> y) -> 1
form4 :: Formula
form4 = C If [C If [V 0, V 1], C T []]

-- form5 = 1 -> x -> y
form5 :: Formula
form5 = C If [C T [], C If [V 0, V 1]]

-- form6 = ~(z v x)
form6 :: Formula
form6 = C Neg [C Or [V 2, V 0]]

constantFormula :: Formula
constantFormula = C Or [C T [], C F []]

incorrectFormula :: Formula
incorrectFormula = C Iff [C Xor [C And [V 0, V 1], C Neg [V 2]], C Or [V 0, V 2, V 3, V 3]]

-- Fast test show
testFormulas = [form1, form2, form3, form4, form5, form6, constantFormula]
runFP = map showFP testFormulas
runSF = map showF testFormulas

-- Задание 1. Напишите функцию correctArity, которая проверяет, что
-- арность каждого оператора, объявленная в модуле BooleanSyntax,
-- совпадает с действительным количеством его аргументов в формуле.

correctArity :: Formula -> Bool
correctArity (V _) = True
correctArity (C op formulas)
  | (arity op) == (length formulas) = all (True ==) $ map correctArity formulas 
  | otherwise = False

-- Значения переменных берутся из окружения (environment).
-- Окружение можно рассматривать как набор значений аргументов
-- в одной строчке таблицы истинности функции.
-- Значения переменной с номером i есть i-й элемент списка (i >= 0).

type Environment = [Domain]

-- Задание 2. Напишите функцию lookupVar, возвращающую значение переменной
-- в окружении.

lookupVar :: Environment -> Var -> Domain
lookupVar = (!!)

-- Задание 3. Напишите функцию eval, возвращающую значение формулы в окружении.
-- Значение операторов возвращаются функцией evalOp в модуле BooleanSyntax.

eval :: Environment -> Formula -> Domain
eval env (V v) = lookupVar env v
eval env (C op formulas) = evalOp op $ map (eval env) formulas

-- Текстовое представление формул

-- Вспомогательная функция, которую можно вызывать в функциях fullParen и showFormula ниже,
-- если встречаются операции с арностью, отличной от 0, 1 или 2

arityError = error "Arity other than 0, 1 or 2"

-- Задание 4. Напишите функцию fullParen, которая возвращает текстовое
-- представление формулы, где каждая состовная подформула с
-- положительным числом аргументов окружена скобками. Переменные и
-- константы (то есть нульарные функции) окружать скобками не нужно.

fullParen :: Formula -> ShowS
fullParen (V v) = varName v
fullParen (C op []) = opText op
fullParen (C op [f]) = showChar '(' . opText op . fullParen f . showChar ')'
fullParen (C op [f1, f2]) = showChar '('  . fullParen f1 . opText op . fullParen f2 . showChar ')'

-- Вариант, учитывающий приоритет и ассоциативность операций

-- Скобки вокруг констант (связок арности 0) не ставятся.
-- Операции арности 1 являются префиксными или отображаются
-- специальным образом. Например, C Neg [f] отображается как ~f
-- в тексте и \overline{f} в LaTeX.

-- Инфиксные операции

-- Пусть данная формула (второй аргумент функции ниже) является левым
-- аргументом операции opExt, а главная операция формулы есть opInt.
-- Скобки вокруг формулы ставятся тогда и только тогда, когда
-- 1) приоритет opExt строго больше приоритета opInt, или
-- 2) приоритет opExt равен приоритету opInt и
--  2а) opExt <> opInt, или
--  2б) opExt = opInt имеет ассоциативность RA или NA.

-- Если данная формула является правым аргументом opExt, то в пункте 2б)
-- нужно заменить RA на LA.

-- Задание 5. Напишите функцию showFormula, которая возвращает текстовое
-- представление формулы, где вставляются только необходимые скобки
-- согласно описанию выше.
-- Первый аргумент: оператор, находящийся непосредственно снаружи формулы
--   (внешний оператор)
-- Второй аргумент: является ли формула левым (True) или правым (False)
--   аргументом внешнего оператора
-- Третий аргумент: формула, которую нужно напечатать

maybeBracket :: Op -> Op -> Bool -> Char -> ShowS
maybeBracket opExt opInt side bracket
  | prec opExt > prec opInt = showChar bracket
  | prec opExt == prec opInt && (b1 || b2) = showChar bracket
  | otherwise = showString ""
  where b1 = opExt /= opInt
        b2 = opExt == opInt && (assoc opExt == NA || assoc opExt == if side then RA else LA)

showFormula :: Op -> Bool -> Formula -> ShowS
showFormula _ _ (V v) = varName v
showFormula _ _ (C op []) = opText op
showFormula opExt side (C opInt [f]) =  maybeLeftBracket . opText opInt . showFormula opInt False f . maybeRightBracket
  where maybeLeftBracket = maybeBracket opExt opInt side '('
        maybeRightBracket = maybeBracket opExt opInt side ')'
showFormula opExt side (C opInt [f1, f2]) =
  maybeLeftBracket . showFormula opInt True f1 . opText opInt . showFormula opInt False f2 . maybeRightBracket
  where maybeLeftBracket = maybeBracket opExt opInt side '('
        maybeRightBracket = maybeBracket opExt opInt side ')'

-- После написания fullParen или showFormula раскоментируйте соответствующий
-- вариант объявления членства типа Formula в классе Show

showFP f = fullParen f ""
showF f = showFormula noOp True f ""

instance Show Formula where
--  show f = fullParen f ""
  show = showF

-- Задание 6. Напишите функцию collectVars1, которая возвращает
-- отсортированный список переменных, входящих в формулу. Каждая
-- переменная входит в список не более одного раза.

collectVars1 :: Formula -> [Int]
collectVars1 = sort . nub . getVars
  where getVars (V v) = [v]
        getVars (C op formulas) = concatMap getVars formulas

-- Прочитайте в Prelude описание классов Enum и Bounded. Обратите внимание,
-- что для типов, которые являются членами класса Enum, доступен синтаксис
-- для последовательностей [a..b] и [a,b..c].

-- Все элементы типа Domain в одном списка.
-- Возможно благодаря тому, что Domain является членом классов Enum и Bounded.

domain :: [Domain]
domain = [minBound .. maxBound]

-- Задание 7. Напишите функцию allEnvs, которая принимает количество n
-- переменных в формуле (вернее, номер максимальной переменной плюс 1)
-- и возвращает список всех окружений длины n в лексикографическом
-- порядке, где порядок на компонентах окружения определяется списком
-- domain.

allEnvs :: Int -> [Environment]
allEnvs 0 = [[]]
allEnvs n = sort [x:xs | x <- domain, xs <- allEnvs (n-1)]

-- Задание 8. Напишите функцию envLength, которая возвращает длину
-- окружения, необходимого для вычисления значения формулы.  Если в
-- формуле нет переменных, то длина равна 0, иначе длина равна
-- максимальному номеру переменной плюс 1.

envLength :: Formula -> Int
envLength = (1+) . maybeMaximum . collectVars1
  where maybeMaximum [] = -1
        maybeMaximum vars = maximum vars

-- Задание 9. Напишите функцию allFormulaEnvs, которая возвращает все
-- окружения фиксированной длины, достаточной для вычисления значения
-- формулы. Окружения должны быть перечислены в лексикографическом порядке.

allFormulaEnvs :: Formula -> [Environment]
allFormulaEnvs = allEnvs . envLength

-- Задание 10. Напишите функцию formulaValues, которая возвращает значения
-- функции на всех наборах аргументов. В таблице истинности это столбец
-- значений функции.

formulaValues :: Formula -> [Domain]
formulaValues f = map (\x -> eval x f) $ allFormulaEnvs f

-- Задание 11. Напишите функцию isConstant c f, которая определяет, является
-- ли формула f константой, принимающей значение c на всех окружениях

isConstant :: Domain -> Formula -> Bool
isConstant c f = all (==c) $ formulaValues f

-- Задание 12. Напишите функцию collectVars2, аналогичную collectVars1,
-- использующую списочную монаду. Список уже определен в Prelude как
-- член класса Monad, поэтому на нём можно использовать запись >>=.

collectVars2 :: Formula -> [Int]
collectVars2 = sort . nub . go 
  where go (V v) = return v
        go (C op fs) = do 
          f <- fs 
          go f

-- Задание 13. Разностный список -- это функция, которая принимает
-- суффикс списка и возвращает целый список, аналогично функциям типа
-- ShowS. Напишите функцию collectVars3, аналогичную collectVars1, но
-- использующие разностные списки.

collectVars3 :: Formula -> [Int]
collectVars3 = error "Неопределенная функция"
