# Object-Oriented Interpreter

This project is an interpreter for a dynamically-typed object-oriented language. The language doesn't fully implement all OO principles yet, however single inheritance, instance and static methods, and instance fields have been implemented so far. For more on the complete description of the languages features, read [here](/language-description.md). 

## Getting Started

These instructions will get you a copy of the project up and running on your local machine for development and testing purposes. See deployment for notes on how to deploy the project on a live system.

### Prerequisites

- [DrRacket](https://download.racket-lang.org/) that is comptabile with Racket 8.11.1


### Running Code

1. Clone this repo
2. Write the program in a text file
3. Optionally run `(parser <source-filepath>)` on the `parser.rkt` file to check for any syntax errors
4. Run `(runcode <source-filepath> <main-class>)` in the `interpret.rkt` file where `main-class` is the class who's main function will execute

The output from the program will populate in the console. In this language, main functions are allowed to return any valid value, not just an exit status. Note that compiler does not force `main` functions to be present, so if the `main-class` specified in `runcode` does not contain a main function, the program will fail. 

## Running the tests

All tests cases are included in the `test` folder of the repo. Since the project was built incrementally from an imperative language, there are earlier versions of testing folders that were used during early development that no longer pass what the current interpreter supports. This is not problematic, as the constructs that those tests contain are supported in the interpreter, just with the addition of classes. If you'd like to add any of your own tests, they can be added in the `tests/individual-test-cases/oo-tests/` directory. 

Tests can be ran in the same way that normal programs are ran. There is functionality to more easily support testing programs against their expected output, however the source program must be named `test<#>.txt`. Given that this style is followed, the `(test <test-num> <main-class>)` function can be used to run a single test, and the `(run-all-tests <test-num>)` will run tests 1 through `test-num`. Expected values and main classes to be executed can be changed in the `expected` and `mains` lists near the bottom of the `interpret.rkt` file. The location of values in these lists will correspond to the programs they are expected output for, i.e. the head of the list corresponds to expected output of test1.

## Built With

* [Racket](https://download.racket-lang.org/releases/8.11.1/doc/index.html) - The underlying language used
