-- Алексей Гладышев
-- wotpricol@mail.ru

module BooleanFormula where

import BooleanSyntax
import Formula hiding (form1, form2, form3, form4)
import qualified Data.List as DL
import Data.Bits
import System.Random
import Control.Monad.State

-- Этот модуль посвящен работе с булевыми формулами в отличие от
-- Formula.hs, который работает с формулами общего вида.

-- Задание

-- 1. Напишите функции, проверяющие принадлежность
-- функции классам Поста. Этих классов пять:
-- 1) функции, сохраняющие False;
-- 2) функции, сохраняющие True;
-- 3) самодвойственные функции;
-- 4) монотонные функции;
-- 5) линейные функции.

-- 2. Напишите функцию rf :: Int -> Int -> R Formula, генерирующую
-- случайные формулы заданной глубины,:r вместе с указанными
-- вспомогательными функциями. Нужно использовать генератор случайных
-- чисел из System.Random.

-- Литература
-- ГС: Гаврилов Г.П., Сапоженко А.А. Задачи и упражнения по
-- дискретной математике. М.: Физматлит, 2005.

-- Проверка на самодвойственность: ГС, с. 64.

-- Проверка на монотонность: ГС, с. 76.

-- Проверка на линейность: ГС, с. 53. Описан метод построения полинома
-- Жегалкина, базирующийся на преобразовании вектора значений функции.
-- Альтернативно: https://ru.wikipedia.org/wiki/Полином_Жегалкина
-- Построение полинома Жегалкина методом Паскаля (то же, что в ГС) или
-- методом треугольника.

-- Примеры формул

-- form1 = x v y -> ~z
form1 :: Formula
form1 = C If [C Or [V 0, V 1], C Neg [V 2]]

-- form2 = xy + ~z <-> x v z
form2 :: Formula
form2 = C Iff [C Xor [C And [V 0, V 1], C Neg [V 2]], C Or [V 0, V 2]]

-- form3 = y <-> z
form3 :: Formula
form3 = C Iff [V 1, V 2]

-- form4 = xy v (z v 0)
form4 = C Or [C And [V 0, V 1], C Or [V 2, C F []]]

-- selfDualForm = ((x y) v (x z)) v (y z)
selfDualForm1 = C Or [C Or [C And [V 0, V 1], C And [V 0, V 2]], C And [V 1, V 2]]
selfDualForm2 = V 0
selfDualForm3 = C Neg [V 0]

monotoneForm = C And [V 0, V 1]
nonMonotoneForm = C Neg [C And [V 0, V 1]]

linearForm = C Xor [V 0, V 1]
nonLinearForm = C Xor [C Xor [V 0, V 1], C And [V 0, V 1]]

-- preservesFalse
preservesFalse :: Formula -> Bool
preservesFalse f = isConstant False f

-- preservesTrue
preservesTrue :: Formula -> Bool
preservesTrue f = isConstant True f

-- selfDual
selfDual :: Formula -> Bool
selfDual f = (negNegFormulaValues f) == (formulaValues f)
    where negNegFormulaValues f = negList $ map (\x -> eval x f) $ map negList $ allFormulaEnvs f
          negList = map not

-- monotone
monotone :: Formula -> Bool
monotone f = isSorted $ formulaValues f
    where isSorted [] = True
          isSorted [x] = True
          isSorted (x:y:xs) = x <= y && isSorted (y:xs)

-- linear
-- Построение полинома Жегалкина делается с помощью метода треугольника Паскаля.
-- Подробнее здесь: https://habr.com/en/post/275527/
getNextTriangleLine :: [Bool] -> [Bool]
getNextTriangleLine [x] = [x]
getNextTriangleLine line = zipWith xor (withoutFirst line) (withoutLast line)
    where withoutFirst = tail
          withoutLast = reverse . drop 1 . reverse

getPascalTriangle :: [Bool] -> [[Bool]]
getPascalTriangle [x] = [[x]]
getPascalTriangle l = (l : (getPascalTriangle $ getNextTriangleLine l))

linear :: Formula -> Bool
linear f = not $ any (True==) $ zipWith (&&) nonlinearitiesList zhegalkinCoefficients
    where zhegalkinCoefficients = map head (getPascalTriangle $ formulaValues f)
          nonlinearitiesList = [(length $ filter (==True) env) > 1 | env <- allFormulaEnvs f]


type R a = State StdGen a
-- StdGen -> (a, StdGen) - значения типа State

-- chooseAction actions k принимает список действий actions, каждое из
-- которых снабжено положительным весом, а также число k. Смысл весов
-- в том, что они определяют распределение вероятностей для действий:
-- если actions = [(p1, a1), ..., (pn, an)] и P = p1 + ... + pn, то
-- действие aj происходит с вероятностью pj/P. Формально
-- chooseAction [(p1, a1), ..., (pn, an)] k возвращает aj, такое что
-- sum_{i=1}^{j-1} pi <= k < sum_{i=1}^j pi.
-- Это не значит, что код должен проверять это условие буквально.
-- Функция должна проходить список один раз.
-- Пример:
-- > map (chooseAction [(2, 1), (3, 2), (1, 3)]) [0..5]
-- [1,1,2,2,2,3]
-- Данная функция не использует случайные числа, а действия могут быть
-- значениями любого типа, не обязательно монадного.
-- Предусловие: n > 0, p1 > 0, ..., pn > 0, 0 <= k < sum_{i=1}^n pi.

chooseAction :: (Ord p, Num p) => [(p, a)] -> p -> a
chooseAction actions k = go actions 0
    where go [] acc = error "ChooseAction :: empty list"
          go ((p, a):xs) acc
            | acc + p > k = a
            | otherwise = go xs (acc + p)

-- Обертка для запуска. Принимает случайное действие и начальное значение
-- для генератора случайных чисел. Возвращает псевдослучайное значение.
runR :: R a -> Int -> a
runR action seed = fst $ runState action (mkStdGen seed)

-- Возвращает случайное число в диапазоне, включая крайние значения
-- Usage:  fst $ runState (randomRange (1,10)) (mkStdGen 47)
--         runR (randomRange (1, 10)) 10

-- state random :: State StdGen a
-- runState (state random) :: StdGen -> (a, StdGen)

randomRange :: Random a => (a, a) -> R a
randomRange range = state $ randomR range

-- Для тестирования: runR (replicateM 10 (randomRange (-2, 2))) 523
-- Здесь replicateM :: Monad m => Int -> m a -> m [a]
-- повторяет действие указанное количество раз

-- Принимает список взвешенных действий, как в chooseAction, и
-- возвращает одно из этих действий случайным образом в соответствии с
-- распределением вероятностей. Действия являются значениями типа R a.
frequency :: [(Int, R a)] -> R a
frequency actions = do
                randomNumber <- randomRange (0, (sum $ map fst actions)-1)
                chooseAction actions randomNumber

-- randomVar n возвращает случайным образом одну из переменных
-- V 0, ..., V (n-1). Сложность по времени и по памяти не должна
-- зависеть от n.
-- Предусловие: n > 0
randomVar :: Int -> R Formula
randomVar n = do
            index_ <- randomRange (0, n-1)
            return (V index_)

-- Возвращает случайную формулу-константу
randomConst :: R Formula
randomConst = frequency [(1, return (C F [])), (1, return (C T []))]

-- Возвращает случайную бинарную связку. Все связки равновероятны.
-- Usage: runR randomBin 4
randomBin :: R Op
randomBin = frequency [(1, return And), (1,  return Or), (1, return If),
                       (1, return Iff), (1,  return Xor), (1, return Nand),
                       (1, return Nor)]

-- Возвращает случайную формулу.
-- Первый аргумент: максимальная глубина формулы.
-- Второй аргумент: максимальное количество переменных в формуле
rf :: Int -> Int -> R Formula
-- Если d = 0, то с вероятностью 10% возвращается константа, 90% -- переменная.
rf 0 n = frequency [(1, randomConst), (9, randomVar n)]
-- Если d > 0, то с вероятностью 1/6 возвращается формула-отрицание, а
-- с вероятностью 5/6 -- формула с бинарной связкой.
rf d n =
    do useNeg <- frequency [(1, return True), (5, return False)]
       if useNeg
       then do f <- rf (d-1) n
               return (C Neg [f])
       else do f1 <- rf (d-1) n
               f2 <- rf (d-1) n
               op <- randomBin
               return (C op [f1, f2])

-- Для тестирования
randomFormula :: Int -> Int -> Int -> Formula
randomFormula depth vars seed = runR (rf depth vars) seed
