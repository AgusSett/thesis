# Formalización de Sistema I con tipo Top

Tesina para el título de Licenciatura en Ciencias de la Computación\
[Departamento de Ciencias de la computación](https://dcc.fceia.unr.edu.ar/), [Universidad Nacional de Rosario](http://www.unr.edu.ar/)

Autor: Agustin Settimo\
Directora: [Cecilia Manzino](https://www.fceia.unr.edu.ar/~ceciliam/)\
Co-Director: [Cistian Sottile](https://cristiansottile.ar/)

## Índice

La mayor parte del código está basado en libro [Programming Language Foundations in Agda](https://plfa.github.io/).

- `Type.agda`: Definición de los tipos del cálculo.
- `IsoType.agda`: Definición de los isomorfismos de tipos.
- `Term.agda`: Definición de los contextos de tipado, términos del cálculo, formas normales, neutrales, y valores.
- `Subs.agda`: Definición de los renombres y substituciones explícitas. Pruebas de propiedades de la substitución. La técnica utilizada está basada en [reducibility-candidates.agda](https://github.com/foones/formal-proofs/blob/master/strong-normalization/reducibility-candidates.agda#L253).
- `Reduction.agda`: Definición de la relación de reducción.
- `IsoTerm.agda`: Definición de la relación de equivalencia entre términos.
- `StrongNorm.agda`: Prueba de normalización fuerte para Sistema I con tipo Top. El código está adaptado y extendido a partir de [StrongNorm2.agda](https://github.com/AndrasKovacs/misc-stuff/blob/master/agda/STLCStrongNorm/StrongNorm2.agda)
- `Progress.agda`: Implementación de la estrategia de reducción. Prueba de la propiedad de progreso.
- `Eval.agda`: Definición de la reducción módulo isomorfismos y la función de evaluación.
