# Курс по функциональному программированию на языке Haskell

## Ссылки на ресурсы, позволяющие использовать Haskell с Jupyter Notebook

https://mmhaskell.com/blog/2019/3/4/shareable-haskell-with-jupyter

https://github.com/gibiansky/IHaskell

https://mybinder.org/v2/gh/gibiansky/IHaskell/master

https://mybinder.org/v2/gh/gibiansky/IHaskell/a992ad83702e55b774de234d77ffd2682d842682


## exam_project
Задача проекта: написать программу, которая манипулирует булевыми формулами.

В частности программа должна проверять членство функции, реализуемой формулой,
в пяти предполных классах Поста:
1) функции, сохраняющие 0
2) функции, сохраняющие 1
3) самодвойственные функции
4) монотонные функции
5) линейные функции

Программа также должна генерировать случайные формулы для составления задач
по дисциплине "Теория дискретных функций". Это не так просто в Haskell,
потому что функция, генерирующая случайные числа, обычно реализуется
как функция с побочными эффектами (изменение состояния генератора), ведь
последовательные вызовы возвращают разные значения. Несмотря на то, что
в Haskell нет побочных эффектов, такое поведение можно реализовать с помощью
конструкции, которая называется монада, и которая широко используется
в Haskell несмотря на свою неочевидность.


## notebboks
Тетрадки, в которых разобраны экзаменационные вопросы.
