;SOLUCION PARA EL PROBLEMA 3-COL MEDIANTE COMPUTACION CELULAR CON MEMBRANAS.

;RAFAEL VALLE MORALES. INGENIERIA INFORMATICA (PLAN 97)

;[ARCHIVO SIN TILDES]

;El problema 3-COL consiste en determinar si un mapa puede ser coloreado unicamente con 3 colores, teniendo
; en cuenta que las regiones contiguas deben tener colores distintos. Toda instancia del problema es codificada
; por un grafo cuyos vertices determinan las distintas regiones del mapa, y cuyas aristas definen la contiguidad de
; dichas regiones. De manera que, los datos de entrada del sistema seran los elementos (vertices y aristas) del grafo
; correspondiente al mapa sobre el que se desea obtener una respuesta.

;TODO BREVE EXPLICACION DEL MODELO DE COMPUTACION CELULAR CON MEMBRANAS BASADO EN TEJIDOS
;TODO BREVE EXPLICACION DEL SISTEMA IMPLEMENTADO (ESTRUCTURAS, REGLAS, HECHOS, INTERFAZ)

;BIBLIOGRAFIA (REFERENCIAS Y DOCUMENTACION)
;REFERENCIAS
;R1. Every planar graph is four colorable - Part1: Discharging
;   [https://projecteuclid.org/euclid.ijm/1256049011]
;R2. Every planar graph is four colorable - Part2: Reducibility
;   [https://projecteuclid.org/euclid.ijm/1256049012]
;R3. Solving 3-COL with Tissue P Systems
;   [http://www.gcn.us.es/4BWMC/vol2/diaz.pdf]
;R4. A uniform family of tP systems with cell division solving 3-COL in a linear time
;   [http://www.sciencedirect.com/science/article/pii/S030439750800251X]

;DOCUMENTACION

;D1.CLIPS Documentation
;   [http://www.clipsrules.net/?q=Documentation]
;D2.CLIPS Basic Reference Guide
;   [https://www.csie.ntu.edu.tw/~sylee/courses/clips/bpg/top.html]
;D3.Conceptos basicos de la computacion celular con membranas
;   [http://www.sema.org.es/ojs/index.php?journal=sema&page=article&op=view&path%5B%5D=191]
;D4.Modelos de computacion celular con membranas
;   [http://www.p-lingua.org/mecosim/matvida/course/Unidad2_Computaci%F3nCelularConMembranas.pdf]
;D5.A CLIPS simulator for Recognizer P Systems with Active Membranes
;   [http://cantor.cs.us.es/2BWMC/bravolpdf/CLIPS.pdf]


;ESTRUCTURAS DE DATOS

;Las celulas se identifican con los valores 0 (entorno), 1 y 2 (celula con datos de entrada). Adicionalmente,
; para identificar cada celula etiquetada por 2, se usa un segundo valor

;Las celulas con la etiqueta 2 (celula con datos de entrada) se identificaran por dos numeros que
; se correpsonden con l

;Para la fase de generacion, en el color de los vertices, se considera T como indicativo
; de transicion hasta la division en la que se sustituye por los colores G y B.

;Para la fase de verificacion, en el color de los vertices, se consideran los colores
; RC, GC y BC como las versiones complementadas de R, G y C.

;En la fase de verificacion, en el color de las aristas, se consideran P y PC como valores
; de transicion hasta obtener los colores R G y B para las mismas.

;ESTRUCTURAS DE DATOS

(deftemplate membrana
  (slot etiqueta)
  (multislot contenido)
)

(deftemplate regla-division ;[elemento-izquierda] -> [elemento-derecha1][elemento-derecha2]
  (slot etiqueta)
  (multislot elemento-izquierda)
  (multislot elemento-derecha1)
  (multislot elemento-derecha2)
)

(deftemplate regla-comunicacion ;(etiqueta-izquierda, elementos-izquierda/elementos-derecha, etiqueta-derecha)
  (slot etiqueta-izquierda)
  (slot etiqueta-derecha)
  (multislot elementos-izquierda)
  (multislot elementos-derecha)
)

(deftemplate instancia-3col ;Define una instancia del problema 3-COL a partir del grafo que lo codifica.
  (slot n-vertices)
  (multislot vertices) ;(vertices , A 1 , A 2 , ... , An ,)
  (slot m-aristas)
  (multislot aristas)  ;(aristas , A 1 2 , A 1 3 , ... , A i j ,) con [1 <= i < j <= n]
)

;FUNCIONES AUXILIARES

(deffunction techo (?valor)
  (if (> ?valor (integer ?valor)) then (+ (integer ?valor) 1) else (integer ?valor))
)

;VARIABLES GLOBALES
(defglobal ?*n-vertices* = 0)
(defglobal ?*m-aristas* = 0)

;REGLAS (INICIALIZACION, DIVISION y COMUNICACION)

;TODO Implementar regla de inicializacion para generar todas las reglas y elementos dependientes de los parametros n y m
;TODO Usar assert para introducir los parametros necesarios numero de vertices (n) y aristas con el format A 1 2 , A 1 3 etc..
; A continuacion por el initial-fact y los parametros se dispara la regla de inicializacion generando los hechos
; de las reglas y las membranas pertinentes
;TODO Incluir en inicializacion mensajes descriptivos del proceso para determinar cuando empieza el proceso real.
;TODO realizar interfaz para pedir los datos indicando el formato

;INICIALIZACION
(defrule lee-instancia-3-col "a partir de los datos de entrada genera los hechos necesarios para inicializar el sistema"

  ?entrada <- (instancia-3col (n-vertices ?n-vertices) (vertices $?vertices)
                              (m-aristas ?m-aristas) (aristas $?aristas))
  =>
  (retract ?entrada)

  ;Guarda el numero de vertices y aristas en variables globales para su uso en la inicializacion del sistema.
  (bind ?*n-vertices* ?n-vertices)
  (bind ?*m-aristas* ?m-aristas)

  ;Variables locales auxiliares.
  (bind ?log2-m (/ (log ?m-aristas) (log 2)))
  (bind ?techo-log2-m (techo ?log2-m))

  ;Las copias de los elementos contador se generan en orden decreciente de indice,
  ; por ejemplo, para el contador a se generan las copias de an, despues de an-1, etc...
  (bind ?indice-a (+ (*  2 ?n-vertices) ?techo-log2-m 12)) ;Indices de los contadores a, 1 ... 2n + [log2(m)] + 12
  (bind ?indice-c (+ (* 2 ?n-vertices) 1))                 ;Indices de los contadores c, 1 ... 2n + 1
  (bind ?indice-d (+ ?techo-log2-m 1))                     ;Indices de los contadores d, 1 ... [log2(m)] + 1
  (bind ?indice-f (+ ?techo-log2-m 7))                     ;Indices de los contadores f, 1 ... [log2(m)] + 7

  ;Numero de copias del primer elemento contador que se genera.
  (bind ?copias-a 1)
  (bind ?copias-c (integer (** 4  ?n-vertices)))        ;4 elevado a n copias de cn+1

  (bind ?copias-d (* (integer (** 2  (- ?indice-d 1)))  ;3 elevado a n copias por 2 elevado a [log2(m)] de d[log2(m)]
                     (integer (** 3 ?n-vertices))))

  (bind ?copias-f (integer (** 3 ?n-vertices)))         ;3 elevado a n copias de f[log2(m) + 6]

  ;En el caso del contador a, solo es necesario una copia de cada elemento, pues unicamente interactuara con ellos la membrana
  ; etiquetada con 1.

  ;En el caso del contador c, inicialmente solo interactua con la membrana etiquetada por 1, pero tras lafase de division es necesario
  ; disponer de tantas copias del ultimo elemento c como membranas con etiqueta 2 se hayan generado. Es decir, 3 elevado a n copias
  ; del elemento c con el ultimo indice posible para dichos contadores.

  ;En el caso del contador d, en cada aplicacion de la regla de comunicacion correspondiente, una membrana etiquetada con 2
  ; se trae 2 copias por cada elemento contador d que tiene. De manera que, al existir 3 elevado a n membranas etiquetada con 2
  ; al final de la fase de division, es necesario generar 3 elevado a n por 2 elevado a [log2(m)].

  ;En el caso del contador f deben generarse 3 elevado a n copias de cada uno, pues estos contadores interactuan con las membranas
  ; con etiqueta 2. Tras la fase de division hay 3 elevado a n membranas con etiqueta 2.

  ;Hechos para la inicializacion de vertices y aristas.
  (assert (inicializa-vertices ?n-vertices $?vertices) ;(, A 1 , A 2 , ... , A n ,)
          (inicializa-aristas ?m-aristas $?aristas))   ;(, A 1 2 , A 1 3 , ... , A i j ,) con 1 <= i < j <= n

  ;Hechos para la inicializacion de los distintos tipos de contadores del sistema.
  ;Las copias indicadas corresponden a las copias a generar del contador cuyo indice se ha especificado en el mismo.
  (assert (inicializa-contadores a ?indice-a ?copias-a)
          (inicializa-contadores c ?indice-c ?copias-c)
          (inicializa-contadores d ?indice-d ?copias-d)
          (inicializa-contadores f ?indice-f ?copias-f))

)

(defrule inicializacion-vertices "introduce en el sistema los elementos referentes a los vertices"

  ?iv <- (inicializa-vertices ?n-vertices $?vi , A ?i , $?vf)

  ?membrana0 <- (membrana (etiqueta 0) ;Entorno
                          (contenido $?c0))

  ?membrana2 <- (membrana (etiqueta 2) ;Entrada
                          (contenido $?c2))

  =>
  (modify ?membrana0 (contenido $?c0 A ?i , R ?i , T ?i , B ?i , G ?i , RC ?i , BC ?i , GC ?i ,))
  (modify ?membrana2 (contenido $?c2 A ?i ,))
  (retract ?iv)

  (if (neq ?n-vertices 1) then (assert (inicializa-vertices (- ?n-vertices 1) $?vi , $?vf)))

)

(defrule inicializacion-aristas "introduce en el sistema los elementos referentes a las aristas"

    ?ia <- (inicializa-aristas ?m-aristas $?ai , A ?i ?j , $?af)

    ?membrana0 <- (membrana (etiqueta 0) ;Entorno
                            (contenido $?c0))

    ?membrana2 <- (membrana (etiqueta 2) ;Entrada
                            (contenido $?c2))

  =>
  (modify ?membrana0 (contenido $?c0 P ?i ?j , PC ?i ?j , R ?i ?j , B ?i ?j , G ?i ?j ,))
  (modify ?membrana2 (contenido $?c2 A ?i ?j ,))
  (retract ?ia)

  (if (neq ?m-aristas 1) then (retract ?ia) (assert (inicializa-aristas (- ?m-aristas 1) $?ai , $?af)))


)

(defrule inicializacion-contadores "genera los contadores necesarios en el entorno"

  ?ic <- (inicializa-contadores ?tipo ?indice ?copias)

  ?membrana0 <- (membrana (etiqueta 0) ;Entorno
                          (contenido $?c0))

  =>
  (retract ?ic)
  (modify ?membrana0 (contenido $?c0 ?tipo ?indice ,))

  (if (> ?copias 1) ;Si el numero de copias no es 1 estamos en los casos de los contadores c y d.
    then (assert (inicializa-contadores ?tipo ?indice (- ?copias 1)))

    else (if (eq ?tipo f) ;Caso del contador f.
           then (if (> ?indice 2)
                  then (assert (inicializa-contadores f (- ?indice 1) (** 3 ?*n-vertices*))))

           else (if (> ?indice 1) ;Casos de los contadores a, c y d con todas las copias del contador i generadas.
                  then (bind ?indice (- ?indice 1))
                       (switch ?tipo
                         (case a then (assert (inicializa-contadores ?tipo ?indice 1)))
                         (case c then (assert (inicializa-contadores ?tipo ?indice (integer (** 2 (- ?indice 1))))))
                         (case d then (assert (inicializa-contadores ?tipo ?indice (* (integer (** 2 (- ?indice 1)))
                                                                                      (integer (** 3 ?*n-vertices*))))))))))

)

;DIVISION
(defrule division
  (regla-division (etiqueta ?etiqueta) ;Selecciona los elementos que definen la regla de division
                  (elemento-izquierda $?elemento-izquierda)
                  (elemento-derecha1 $?elemento-derecha1)
                  (elemento-derecha2 $?elemento-derecha2))

  ?membrana <- (membrana (etiqueta ?etiqueta)
                         (contenido $?ci , $?elemento-izquierda , $?cf))

  =>
  (retract ?membrana)

  (assert (membrana (etiqueta ?etiqueta)
                    (contenido $?ci , $?elemento-derecha1 , $?cf))

          (membrana (etiqueta ?etiqueta)
                    (contenido $?ci , $?elemento-derecha2 , $?cf)))

)

;COMUNICACION
(defrule comunicacion
  (regla-comunicacion (etiqueta-izquierda ?etiqueta-izquierda)
                      (etiqueta-derecha ?etiqueta-derecha)
                      (elementos-izquierda $?elementos-izquierda)
                      (elementos-derecha $?elementos-derecha))

  ?membrana1 <- (membrana (etiqueta ?etiqueta-izquierda)
                          (contenido $?ci1 , $?elementos-izquierda , $?cf1))
  ?membrana2 <- (membrana (etiqueta ?etiqueta-derecha)
                          (contenido $?ci2 , $?elementos-derecha , $?cf2))

  =>
  (modify ?membrana1 (contenido $?ci1 , $?elementos-derecha , $?cf1))
  (modify ?membrana2 (contenido $?ci2 , $?elementos-izquierda , $?cf2))

)

;TODO Implementar regla para mostrar el resultado final a partir de la entrada dada.
;TODO  reseteat las variables globales en realidad no sera necesario pues termina la aplicacion y habria que volverla a cargar.

;DATOS INICIALES

;TODO Usar dos hechos iniciales comentados para los 2 ejemplos que disparen automaticamente las reglas de inicializacion

(deffacts tp-system ;Especificacion del sistema P basado en tejidos con division celular para el problema 3-COL

  ;MEMBRANAS
  ;La membrana 0 representa al entorno (salida) y requiere ser inicializada con datos de una instancia concreta del problema.
  ; Ademas contiene el resto de elementos necesarios para el sistema. [0 - {yes, no}]
  (membrana (etiqueta 0)
            (contenido , b , D , S , N ,)) ;Constantes presentes para cualquier instancia del problema

  (membrana (etiqueta 1) ;El estado inicial de la membrana 1 es igual para cualquier instancia del problema.
            (contenido , a 1 , b , c 1 , yes , no ,))

  ;La membrana 2 contiene, entre otros, los elementos de entrada que representan una instancia del problema, por tanto
  ; tambien requiere ser inicializada.
  (membrana (etiqueta 2)
            (contenido , D ,))

  ;ESTRUCTURA REGLAS DE DIVISION
  (regla-division (etiqueta 2) (elemento-izquierda A i) (elemento-derecha1 R i) (elemento-derecha2 T i)) ;r1i
  (regla-division (etiqueta 2) (elemento-izquierda T i) (elemento-derecha1 B i) (elemento-derecha2 G i)) ;r2i

  ;Instancias de las reglas de division
  ;(regla-division (etiqueta 2) (elemento-izquierda A 1) (elemento-derecha1 R 1) (elemento-derecha2 T 1)) ;R11
  ;(regla-division (etiqueta 2) (elemento-izquierda A 2) (elemento-derecha1 R 2) (elemento-derecha2 T 2)) ;R12
  ;(regla-division (etiqueta 2) (elemento-izquierda A 3) (elemento-derecha1 R 3) (elemento-derecha2 T 3)) ;R13
  ;(regla-division (etiqueta 2) (elemento-izquierda T 1) (elemento-derecha1 B 1) (elemento-derecha2 G 1)) ;R21
  ;(regla-division (etiqueta 2) (elemento-izquierda T 2) (elemento-derecha1 B 2) (elemento-derecha2 G 2)) ;R22
  ;(regla-division (etiqueta 2) (elemento-izquierda T 3) (elemento-derecha1 B 3) (elemento-derecha2 G 3)) ;R23

  ;ESTRUCTURA REGLAS DE COMUNICACION (1 <-> 0)
  (regla-comunicacion (etiqueta-izquierda 1) (etiqueta-derecha 0) (elementos-izquierdos a i) (elementos-derechos a i+1))                ;r3i
  (regla-comunicacion (etiqueta-izquierda 1) (etiqueta-derecha 0) (elementos-izquierdos c i) (elementos-derechos c i+1 , c i+1))        ;r4i

  ;ESTRUCTURA REGLAS DE COMUNICACION (1 <-> 2)
  (regla-comunicacion (etiqueta-izquierda 1) (etiqueta-derecha 2) (elementos-izquierdos c 2n+1) (elementos-derechos D))                 ;r5

  ;ESTRUCTURA REGLAS DE COMUNICACION (2 <-> 0)
  (regla-comunicacion (etiqueta-izquierda 2) (etiqueta-derecha 0) (elementos-izquierdos c 2n+1) (elementos-derechos d 1 , E))           ;r6
  (regla-comunicacion (etiqueta-izquierda 2) (etiqueta-derecha 0) (elementos-izquierdos d i) (elementos-derechos d i+1 , d i+1))        ;r7i
  (regla-comunicacion (etiqueta-izquierda 2) (etiqueta-derecha 0) (elementos-izquierdos E) (elementos-derechos e , f 2))                ;r8
  (regla-comunicacion (etiqueta-izquierda 2) (etiqueta-derecha 0) (elementos-izquierdos f i) (elementos-derechos f i+1))                ;r9i
  (regla-comunicacion (etiqueta-izquierda 2) (etiqueta-derecha 0) (elementos-izquierdos d tlog2m+1 , A i j) (elementos-derechos P i j)) ;r10ij
  (regla-comunicacion (etiqueta-izquierda 2) (etiqueta-derecha 0) (elementos-izquierdos P i j) (elementos-derechos R i j , PC i j))     ;r11ij
  (regla-comunicacion (etiqueta-izquierda 2) (etiqueta-derecha 0) (elementos-izquierdos PC i j) (elementos-derechos B i j , G i j))     ;r12ij
  (regla-comunicacion (etiqueta-izquierda 2) (etiqueta-derecha 0) (elementos-izquierdos R i , R i j) (elementos-derechos R i , RC j))   ;r13ij
  (regla-comunicacion (etiqueta-izquierda 2) (etiqueta-derecha 0) (elementos-izquierdos B i , B i j) (elementos-derechos B i , BC j))   ;r14ij
  (regla-comunicacion (etiqueta-izquierda 2) (etiqueta-derecha 0) (elementos-izquierdos G i , G i j) (elementos-derechos G i , GC j))   ;r15ij
  (regla-comunicacion (etiqueta-izquierda 2) (etiqueta-derecha 0) (elementos-izquierdos R j , RC j) (elementos-derechos bb))            ;r16j
  (regla-comunicacion (etiqueta-izquierda 2) (etiqueta-derecha 0) (elementos-izquierdos B j , BC j) (elementos-derechos bb))            ;r17j
  (regla-comunicacion (etiqueta-izquierda 2) (etiqueta-derecha 0) (elementos-izquierdos G j , GC j) (elementos-derechos bb))            ;r18j
  (regla-comunicacion (etiqueta-izquierda 2) (etiqueta-derecha 0) (elementos-izquierdos e , bb) (elementos-derechos))                   ;r19
  (regla-comunicacion (etiqueta-izquierda 2) (etiqueta-derecha 0) (elementos-izquierdos f tlog2m+7 , e) (elementos-derechos T))         ;r20

  ;ESTRUCTURA REGLAS DE COMUNICACION (2 <-> 1)
  (regla-comunicacion (etiqueta-izquierda 2) (etiqueta-derecha 1) (elementos-izquierdos T) (elementos-derechos))                        ;r21

  ;ESTRUCTURA REGLAS DE COMUNICACION (1 <-> 0)
  (regla-comunicacion (etiqueta-izquierda 1) (etiqueta-derecha 0) (elementos-izquierdos b , T) (elementos-derechos S))                  ;r22
  (regla-comunicacion (etiqueta-izquierda 1) (etiqueta-derecha 0) (elementos-izquierdos S , yes) (elementos-derechos))                  ;r23
  (regla-comunicacion (etiqueta-izquierda 1) (etiqueta-derecha 0) (elementos-izquierdos a 2n+tlog2m+12 , b) (elementos-derechos N))     ;r24
  (regla-comunicacion (etiqueta-izquierda 1) (etiqueta-derecha 0) (elementos-izquierdos N no) (elementos-derechos))                     ;r25

  ;Instancias de las reglas de division
  ;(regla-comunicacion (etiqueta-izquierda 1) (etiqueta-derecha 0) (elementos-izquierda a 1) (elementos-derecha a 2))


)
