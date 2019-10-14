# The Machine Learning Server

This is a simple socket-based server application that allows a machine
learning approach to interact with KeY.

## Data transfer

Communication works via textually (JSON) represented commands.  over a
socket interface (or a pipe ...)  Data is transferred as JSON
objects. In the following the input `comm(arg=value:str, arg2=42:int)`
is shorthand for the JSON object `{ "command":"comm", "arg":"value",
"arg2":42 }`

For example, the command to load "test.key" would be represented as
`{ "command": "loadFile", "filename": "test.key" }`.

For readability, it is shown here as "loadFile(filename:str)".


In case of the result, the master key is not `command` but
`response`. That is, `error(message="wrong":str)` is, hence,
`{ "response":"error", "message":"wrong" }`

In the error case, the server may choose to add the exception class to
the returned object. The stacktrace is only shown on the server's
console.

## Communication between machine learning tool and KeY.

The outside tool acts as master and instructs KeY to appy individual
tactics to chosen proof goals.

Feature extraction will mainly happen on the KeY side.

Tactic application must be reversible.

## Commands

Initiated by the learning tool, responses by KeY. may be asynchronous.

### Loading of proof

````
   >    load(filename:str)
   <    success
or <    error(message:str)
````

Discards old proof from memory. load new proof obligation.

### Listing all tactics

````
   >    tactics
   <    success(tactics: str[])
or <    error(message:str)
````

### Executing a tactic

````
   >    execute(id: int, tactic: str)
   <    success(ids: int[])
or <    error(message:str)
````

in particular: error if obligation id is not an open goal
`ids` may be empty if closing

### Prune a proof / Undo execution

````
   >    rewind(id: int)
   <    success
or <    error(message:str)
````

### Evaluate obligation

Feature extraction

````
   >    features(id: int)
   <    success(id:int, features...)
or <    error(message:str)
````

The resulting objects lists a number of features. Defined below (well,
some day ...)

### Retrieve an AST

AST transfer

````
   >    ast(id: int)
   <    success(id: int, antecedent: term[], succedent: term[]
or <    error(message: str)
````
with `term` the recursive structure `{ "op":"...", "op_class":"...", children:term[] }`.


# Invoking the server

The server can be invoked using

    ../gradlew run

on unix-like shells and

    ..\gradlew.bat run
    
on Windows. Add `--args=--screen` if you want to have the KeY window
opened for debugging purposed.

# Tactic definitions

The rulesets for the tactics are defined in the file
`src/main/resources/org/key_project/machlearning/filterRulesets.xml`
