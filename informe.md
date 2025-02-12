# DeL
DeL es un lambda-cálculo con un sistema de tipos dependientes.
Está inspirado en la teoría de tipos de Martin-Löf, y en lenguages
modernos como [Coq](https://coq.inria.fr/)
y [Agda](https://agda.readthedocs.io/).


Cuenta con un sistema de tipos muy expresivo,
el cual permite términos arbitrarios en las expresiones de tipo.
Esto permite expresar, por ejemplo, igualdad de términos (el operador de
igualdad es un constructor de tipo built-in).

Los tipos estan comprendidos en un [sistema de Universos](https://agda.readthedocs.io/en/latest/language/sort-system.html#sort-system)
(`Sort`) jerárquico:
para un término poder considerarse un tipo, tiene que tener tipo
`Set i`, con `i` perteneciente a los Naturales.
El sistema no es cumulativo, y vale `Set i : Set i + 1` para todo i.

Además, permite recursión primitiva con el operador `rec`, o `let rec`
en top level; permite análisis por casos con la cláusula `elim`;
y permite definicion de datatypes arbritrarios 
(con algunas restricciones) con la cláusula `data`, con un estilo muy similar a Agda.

Tambien cuenta con una definicion inductiva de los Naturales built-in,
con el unico proposito de permitir literales en sintaxis concreta.

La sintáxis concreta está dada por:

    term t,u := 0,1,2,...
                suc,
                Nat,
                refl,
                t = u,
                x,
                t u,
                \(x y .. : A) (m n ... : B). t,
                fix f (x y ... : A) (m n ... : B). t,
                A -> B,
                (x : A) -> B,
                elim t { c1 := t ; ... ; cn := u },
                s,
                t : A

    vars x,y,m,n,f
    
    constructores c1,c2,...

    type A,B,C := t

    sort s := Set,
              Set i     i >= 0


Conceptualmente, los posibles términos son:
- naturales
- el constructor `suc : Nat -> Nat`
- el tipo `Nat`
- el tipo igualdad
- el testigo de igualdad `refl : t = t` para todo `t`
- variables (globales o ligadas)
- aplicación y abstracción lambda
- abstracción `fix`, donde `f` puede aparecer en el cuerpo
- tipos función, donde el argumento puede estar nombrado
- eliminación por casos, tanto para `Nat` y `=` como para tipos
inductivos definidos por el usuario
- sorts o universos indizados por los naturales 
(`Set` es azúcar sintáctica para `Set 0`)
- términos anotados

Las definiciones globales son de la forma:
    
    let val : A := t

    let fun (x y : A) (z : B) (m n : Nat) : C := t

    let rec rec_fun (x y : A) (m n : Nat) : B := t

En el segundo caso, `x` e `y` pueden aparecer en `B`,
y `x`, `y`, `m`, y `n` pueden aparecer en C.

En el último caso, `rec_fun` puede aparecer en `t`,
aunque solo aplicado a términos estructuralmentes menores a `x`.

En realidad, es solo ázucar sintáctica para:

    let rec_fun : (x y : A) -> (m n : Nat) : B :=
        fix rec_fun (x y : A) (m n : Nat). t

que a su vez se reduce a:

    let rec_fun : (x y : A) -> (m n : Nat) : B :=
        fix rec_fun (x : A). \(y : A).(m n : Nat). t

El lenguaje interno solo considera binders con un solo argumento,
por lo que esta última expresión también tiene azúcar sintáctico.

Internamente, las declaraciones no son tipadas (ni toman argumentos).
La primera definición, luego de elaborarse, luce así:

    let val := t : A

Por último, las definiciones de tipos inductivos son de
la forma:

    data T : (x1 y1 ... : A1) -> (x2 y2 ... : A2) -> ... ->  Set i {
        c1 : (x11 y11 : A11) -> ... -> T a11 b11 ... ;
        c2 : ... ;
        ...
        cn : ...
    }

donde `a11` y `b11` son del tipo `A1`.

Por ejemplo, el tipo indizado de los naturales menores a un `n` dado:

    data Fin : Nat -> Set {
        fin_zero : (n : Nat) -> Fin (suc n) ;
        fin_suc  : (n : Nat) -> Fin n -> Fin (suc n) 
    }

### Estructura del proyecto

#### Common
Definiciones comunes a todo el proyecto.

#### Context

Definicion del contexto de tipado y evaluación.

#### Datatype

Definiciones en relación a los datatypes.

Se implementan algunos chequeos sintácticos utilizados
en la etapa de elaboración, tal como chequeo de nombres repetidos,
y verificar que los tipos de los constructores sean coherentes.

También se implementan chequeos de soundness. Particularmente, se tiene:

- Chequeo de sort: se verifica que ningun argumento de los
constructores habite un `Sort` mayor al declarado para el datatype.
Se realiza para evitar paradojas del estilo de la de Rusell.
Esto imposibilita la definición de tipos parametrizados
(como `List`, `Pair`, etc). Una posible (e interesante) extensión del lenguaje sería permitir parámetros de tipo.
- Chequeo de [Positividad](https://coq.inria.fr/doc/v8.19/refman/language/core/inductive.html#positivity-condition): se verifica que el tipo definido solo aparezca
en posiciones *positivas* en los tipos de los constructores.

#### Elab

Etapa de elaboración de términos superficiales, posterior
a la etapa de parsing. Aquí se realiza el desugaring y
algunos chequeos sintácticos simples.

#### Error

Definiciones de errores.

#### Lang

Definiciones propias del lenguaje:
representación superficial, representación interna,
declaraciones, etc.

#### Main

Módulo principal del lenguaje. Se carga el archivo,
se parsea, elabora, se chequean tipos, se evalúa la
función `main`, y se imprimen los resultados en pantalla.

#### MonadTypeCheck

Interfaz para la mónada utilizada para el typechecking
y evaluación.

#### Parse

Parseo de términos, implementado con la libreria
`Text.Parsec`.

#### PPrint

Pretty printing de términos y errores, implementado con la
librería `Prettyprinter`.

#### Reduce

Beta y eta reducción de términos. Se utiliza un modelo
de evaluación similar a la máquina CEK vista en la materia
Compiladores. Se realiza reducción normal, i.e. se evalúa
dentro de las abstracciones, y luego se eta-reduce.
Siempre se realiza luego del typechecking, para garantizar terminación.

Es una pieza fundamental para el chequeo de tipos, ya que las expresiones de tipo pueden contener términos arbitrarios sin beta reducir.

#### Resugar

Se resugarean los términos antes de imprimirlos.
Debido a que el lenguaje es locally nameless, se tiene especial cuidado con las variables `Free`. Esto sucede solo
en los mensajes de error, ya que un término cerrado no tiene, por definición, variables libres.

#### Substitution

Definiciones para tratar con variables y sustituciones.

#### Termination

Se implementa un [chequeo de terminación](https://arxiv.org/abs/2407.06924) para las funciones
recursivas. El chequeo es puramente sintáctico: se verifica
que el operador recursivo siempre esté aplicado, y que el primer argumento sea estructuralmente menor al primer
argumento de la definición de la función.

Esto sucede únicamente cuando se realiza pattern matching
sobre este argumento: los argumentos de los constructores
en cada caso se consideran subestructurales.

Por ejemplo:
    
    fix f (n : Nat). elim n {
        zero := ... ;
        suc m := ...
    }
En este caso, `m` es estructuralmente menor a `n`
y podría llamarse recursivamente a `f` con `m` como primer argumento.

Una extensión posible sería permitir más de un argumento recursivo,
posiblemente tomando un orden subestructural lexicográfico.

#### Transitive

Representación de relaciones transitivas. Se utiliza en
el módulo `Termination`.

#### TypeCheck

Inferencia y chequeo de tipos. Se cuenta con dos modos:
`infer` y `check`. El primero es el que se utiliza al
chequear una definición. Solo se pasa al modo de chequeo
cuando se cuenta con una anotación de tipo. Hay algunos
términos (por ejemplo, cláusulas `fix`) que no pueden
ser inferidos (solo chequeados).

En general basta con una cantidad de anotaciones razonable
para que la inferencia funcione.

Este módulo cuenta con llamadas a `Reduce`, ya que es
necesario contar con los tipos en forma normal para
la mayoría de los chequeos.

#### Unify

Se implementa un algoritmo de unificación simple para
los términos del lenguaje, inspirado por Agda.
La unificación se realiza dentro de la cláusula `elim`:
se unifican los parámetros del datatype eliminado, y el
término eliminado con el constructor de cada caso.

La unificación permite definir el eliminador j de la 
igualdad, así como el principio lógico de sustitución; también 
permite derivar principios tácitos del lenguaje, tal como
el axioma que dicta que dos constructores distintos son,
efectivamente, distintos.

    let j_elim (A : Set) (C : A -> A -> Set)
            (x y : A) (r : x = y)
            (j : (x : A) -> C x x) : C x y := elim r {
        refl := j x
    }


    let subst (A : Set) (P : A -> Set)
        (x y : A) (r : x = y)
        (p : P x) : P y := elim r {
            refl := p
    }


    data Bot : Set {}

    let neq (A : Set)(x y : A) : Set := (x = y) -> Bot

    let zero_neq_suc (n : Nat) : neq Nat zero (suc n) :=
    \(r : 0 = suc n). elim r {}

Por otro lado, la unificación permite descartar
casos absurdos en el pattern-matching. Veamos, por ejemplo:

    data lt : Nat -> Nat -> Set {
        zero_lt : (n : Nat) -> 0 lt n ;
        suc_lt : (m n : Nat) -> lt m n -> lt (suc m) (suc n)
    }

    let foo (n : Nat) (r : lt 0 n) : Nat := elim r {
        zero_lt _ := 0
    }

    let bar (m : Nat) : Nat := elim (suc m) {
        suc m' := 0
    }

En ambos casos, aunque triviales, solo deben incluirse los
casos coherentes:
- en `foo`, `lt 0 n` se intenta unificar sin éxito con
`lt (suc x) (suc y)` (donde `x` e `y` son variables frescas),
por lo que ese caso se descarta como absurdo;
- en `bar`, `suc m` se intenta unificar sin éxito con
`zero` y este caso se descarta como absurdo.


En última instancia, la unificación solo se realiza sobre
variables, por lo que muchas definiciones deben ser abstraídas para que el sistema pueda chequear su tipo.

#### UnionFind

Implementación de una estructura unioin-find, utilizada en el
módulo `Unify`. Utiliza la librería `Data.DisjointSet` del
paquete `disjoint-conteiners`.

### Ejecución

Para compilar el proyecto:

    cabal build DeL

El lenguaje se corre con el comando:

    cabal exec DeL test.del

Si se quiere evaluar e imprimir un término `t`, debe
incluirse una definición del tipo:

    let main : ... := t

Posibles extensiones serían poder cargar mas de un archivo y
contar con un modo interactivo.