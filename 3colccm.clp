;SOLUCION PARA EL PROBLEMA 3-COL MEDIANTE COMPUTACION CELULAR CON MEMBRANAS.

;RAFAEL VALLE MORALES. INGENIERIA INFORMATICA (PLAN 97)

;[ARCHIVO SIN TILDES]

;El problema 3-COL consiste en determinar si un mapa puede ser coloreado unicamente con 3 colores, teniendo
; en cuenta que las regiones contiguas deben tener colores distintos. Toda instancia del problema es codificada
; por un grafo cuyos vertices determinan las distintas regiones del mapa, y cuyas aristas definen la contiguidad de
; dichas regiones. De manera que, los datos de entrada del sistema seran los elementos (vertices y aristas) del grafo
; correspondiente al mapa sobre el que se desea obtener una respuesta.

;TODO REVISAR TEXTO EN SECCION ESTRUCTURAS DE DATOS, FUE HECHO AL PRINCIPIO Y HAN CAMBIADO MUCHAS COSAS xD
;TODO BREVE EXPLICACION DEL MODELO DE COMPUTACION CELULAR CON MEMBRANAS BASADO EN TEJIDOS
;TODO BREVE EXPLICACION DEL SISTEMA IMPLEMENTADO (ESTRUCTURAS DE DATOS, REGLAS, HECHOS, INTERFAZ, USO DE INTERFAZ Y EJEMPLOS PREDEFINIDOS)

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
(defglobal ?*n-vertices* = 0
           ?*m-aristas* = 0
           ?*techo-log2-m* = 0)

;REGLAS (INICIALIZACION, DIVISION y COMUNICACION)

;TODO Implementar regla para mostrar el resultado final a partir de la entrada dada. Necesidad de funcion contar elementos x por ejemplo ¿?
;TODO Crear dos ejemplos con deffacts comentados para seleccionarlos y asi lanzar el sistema automaticamente si se desea.
;TODO Implementar regla para lanzar interfaz de usuario.
;TODO Incluir en inicializacion mensajes descriptivos del proceso para determinar cuando empieza el proceso real.
;TODO Incluir mensajes descriptivos a lo largo del proceso.

;INICIALIZACION
(defrule lee-instancia-3-col "a partir de los datos de entrada genera los hechos necesarios para inicializar el sistema"

  ?entrada <- (instancia-3col (n-vertices ?n-vertices) (vertices $?vertices)
                              (m-aristas ?m-aristas) (aristas $?aristas))
  =>
  (retract ?entrada)

  ;Guarda en variables globales el numero de vertices y aristas, necesarios para la inicializacion del sistema.
  (bind ?*n-vertices* ?n-vertices)
  (bind ?*m-aristas* ?m-aristas)

  ;Guarda en una variable global el valor del techo del logaritmo en base 2 de m, necesario para la inicializacion del sistema.
  (bind ?log2-m (/ (log ?m-aristas) (log 2)))
  (bind ?*techo-log2-m* (techo ?log2-m))

  ;Las copias de los elementos contador se generan en orden decreciente de indice,
  ; por ejemplo, para el contador a se generan las copias de an, despues de an-1, etc...
  (bind ?indice-a (+ (*  2 ?n-vertices) ?*techo-log2-m* 12)) ;Indices de los contadores a, 1 ... 2n + [log2(m)] + 12
  (bind ?indice-c (+ (* 2 ?n-vertices) 1))                   ;Indices de los contadores c, 1 ... 2n + 1
  (bind ?indice-d (+ ?*techo-log2-m* 1))                     ;Indices de los contadores d, 1 ... [log2(m)] + 1
  (bind ?indice-f (+ ?*techo-log2-m* 7))                     ;Indices de los contadores f, 1 ... [log2(m)] + 7

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

  ;Hecho para la inicializacion de ciertas constantes del sistema.
  ;Dichas constantes, concretamente E, e, T y z, interactuan con las membranas etiquetadas por 2. Luego es necesario generar
  ; las copias necesarias en funcion de la instancia del problema especificado. Es decir, 3 elevado a n copias.
  (assert (inicializa-constantes))

  ;Hecho para la inicializacion de las reglas del sistema.
  ;Dichas reglas se generan en funcion de la instancia del problema especificado.
  (assert (inicializa-reglas))

)

(defrule inicializacion-vertices "introduce en el sistema los elementos referentes a los vertices"

  ?iv <- (inicializa-vertices ?pendientes $?vi , A ?i , $?vf)

  ?membrana0 <- (membrana (etiqueta 0) ;Entorno
                          (contenido $?c0))

  ?membrana2 <- (membrana (etiqueta 2) ;Entrada
                          (contenido $?c2))

  =>
  (retract ?iv)

  ;Genera la lista de elementos referentes al vertice con indice i para despues insertarla en el entorno.
  ; Ademas, para cada elemento crea 3 elevado a n copias, pues cada elemento asociado a un vertice interactua con cada
  ; membrana etiquetada por 2. De manera que interactua con 3 elevado a n membranas.
  (bind ?vertices (create$ A ?i , R ?i , T ?i , B ?i , G ?i , RC ?i , BC ?i , GC ?i ,))
  (bind ?k 1)
  (while (< ?k (integer (** 3 ?*n-vertices*)))
         (bind ?vertices (insert$ ?vertices 1 A ?i , R ?i , T ?i , B ?i , G ?i , RC ?i , BC ?i , GC ?i ,))
         (bind ?k (+ ?k 1)))

  (modify ?membrana0 (contenido $?c0 ?vertices)) ;Entorno

  ;En la membrana de entrada solo es necesario incluir el vertice correspondiente.
  (modify ?membrana2 (contenido $?c2 A ?i ,))

  (if (neq ?pendientes 1) then (assert (inicializa-vertices (- ?pendientes 1) $?vi , $?vf)))

)

(defrule inicializacion-aristas "introduce en el sistema los elementos referentes a las aristas"

    ?ia <- (inicializa-aristas ?pendientes $?ai , A ?i ?j , $?af)

    ?membrana0 <- (membrana (etiqueta 0) ;Entorno
                            (contenido $?c0))

    ?membrana2 <- (membrana (etiqueta 2) ;Entrada
                            (contenido $?c2))

  =>
  (retract ?ia)

  ;Genera la lista de elementos referentes a la arista con indices i j para despues insertarla en el entorno.
  ; Ademas, para cada elemento crea 3 elevado a n copias, pues cada elemento asociado a una arista interactua con cada
  ; membrana etiquetada por 2. De manera que interactua con 3 elevado a n membranas.
  (bind ?aristas (create$ P ?i ?j , PC ?i ?j , R ?i ?j , B ?i ?j , G ?i ?j ,))
  (bind ?k 1)
  (while (< ?k (integer (** 3 ?*n-vertices*)))
         (bind ?aristas (insert$ ?aristas 1 P ?i ?j , PC ?i ?j , R ?i ?j , B ?i ?j , G ?i ?j ,))
         (bind ?k (+ ?k 1)))

  (modify ?membrana0 (contenido $?c0 ?aristas)) ;Entorno

  ;En la membrana de entrada solo es necesario incluir la arista correspondiente.
  (modify ?membrana2 (contenido $?c2 A ?i ?j ,))

  (if (neq ?pendientes 1) then (assert (inicializa-aristas (- ?pendientes 1) $?ai , $?af)))

)

(defrule inicializacion-contadores "genera los contadores necesarios en el entorno"

  ;La inicializacion comienza en orden decreciente de los indices. Por ejemplo an, an-1, etc...
  ?ic <- (inicializa-contadores ?tipo ?indice ?copias)

  ?membrana0 <- (membrana (etiqueta 0) ;Entorno
                          (contenido $?c0))

  =>
  (retract ?ic)

  ;Genera la lista de elementos referentes al contador con indice i para despues insertarla en el entorno.
  ; Ademas, para cada elemento contador crea un numero determinado de copias en funcion de las membranas que
  ; interactuaran con el mismo. En la regla inicial lee-instancia-3-col hay mas informacion al respecto.
  (bind ?contadores (create$ ?tipo ?indice ,))
  (bind ?k 1)
  (while (< ?k ?copias)
         (bind ?contadores (insert$ ?contadores 1 ?tipo ?indice ,))
         (bind ?k (+ ?k 1)))

  (modify ?membrana0 (contenido $?c0 ?contadores))

  (if (eq ?tipo f) ;Caso del contador f que termina en el indice 2 en lugar del 1.
    then (if (> ?indice 2)
           then (assert (inicializa-contadores f (- ?indice 1) (integer (** 3 ?*n-vertices*)))))

    else (if (> ?indice 1) ;Casos de los contadores a, c y d que terminan en el indice 1.
           then  (bind ?indice (- ?indice 1)) ;Proximo indice de los contadores que hay que inicializar.
           (switch ?tipo
                    (case a then (assert (inicializa-contadores ?tipo ?indice 1)))
                    (case c then (assert (inicializa-contadores ?tipo ?indice (integer (** 2 (- ?indice 1))))))
                    (case d then (assert (inicializa-contadores ?tipo ?indice (* (integer (** 2 (- ?indice 1)))
                                                                                 (integer (** 3 ?*n-vertices*)))))))))

)

(defrule inicializacion-constantes "genera ciertas constantes necesarias en el entorno"

  ?ic <- (inicializa-constantes)

  ?membrana0 <- (membrana (etiqueta 0) ;Entorno
                          (contenido $?c0))

  =>
  (retract ?ic)

  ;Genera la lista de ciertos elementos constantes para despues insertarla en el entorno. Para cada elemento
  ; se crean 3 elevado a n copias, pues interactuan con las membranas etiquetadas con 2.
  (bind ?constantes (create$ E , e , T , z ,))
  (bind ?k 1)
  (while (< ?k (integer (** 3 ?*n-vertices*)))
         (bind ?constantes (insert$ ?constantes 1 E , e , T , z ,))
         (bind ?k (+ ?k 1)))

  (modify ?membrana0 (contenido $?c0 ?constantes)) ;Entorno

)

(defrule inicializacion-reglas "genera las reglas del sistema a partir de la instancia del problema 3-COL especificada"

  ?ir <- (inicializa-reglas)

  =>
  (retract ?ir)

  ;REGLAS DE COMUNICACION (1 <-> 0)
  (assert (regla-comunicacion (etiqueta-izquierda 1) (etiqueta-derecha 0)
                              (elementos-izquierda a (+ (* 2 ?*n-vertices*) ?*techo-log2-m* 12) , b) (elementos-derecha N)))  ;r24

  (bind ?k 1)
  (while (<= ?k (+ (* 2 ?*n-vertices*) ?*techo-log2-m* 11)) ;k = 1 ... 2n + [log2(m)] + 11

    (assert (regla-comunicacion (etiqueta-izquierda 1) (etiqueta-derecha 0)
                                (elementos-izquierda a ?k) (elementos-derecha a (+ ?k 1)))) ;r3k

    (if (<= ?k (* 2 ?*n-vertices*)) ;k = 1 ... 2n
      then (assert (regla-comunicacion (etiqueta-izquierda 1) (etiqueta-derecha 0)
                                       (elementos-izquierda c ?k) (elementos-derecha c (+ ?k 1) , c (+ ?k 1)))))  ;r4k


    (if (<= ?k ?*n-vertices*)       ;k = 1 ... n
      then (assert ;REGLAS DE DIVISION
                   (regla-division (etiqueta 2)
                                   (elemento-izquierda A ?k) (elemento-derecha1 R ?k) (elemento-derecha2 T ?k))   ;r1k
                   (regla-division (etiqueta 2)
                                   (elemento-izquierda T ?k) (elemento-derecha1 B ?k) (elemento-derecha2 G ?k))   ;r2k

                  ;REGLAS DE COMUNICACION (2 <-> 0)
                  (regla-comunicacion (etiqueta-izquierda 2) (etiqueta-derecha 0)
                                      (elementos-izquierda R ?k , RC ?k) (elementos-derecha z))   ;r16k
                  (regla-comunicacion (etiqueta-izquierda 2) (etiqueta-derecha 0)
                                      (elementos-izquierda B ?k , BC ?k) (elementos-derecha z))   ;r17k
                  (regla-comunicacion (etiqueta-izquierda 2) (etiqueta-derecha 0)
                                      (elementos-izquierda G ?k , GC ?k) (elementos-derecha z)))  ;r18k

            (bind ?l 1)
            (while (< ?l ?k)        ;1 <= l < k <= n
              (assert (regla-comunicacion (etiqueta-izquierda 2) (etiqueta-derecha 0)
                                          (elementos-izquierda d (+ ?*techo-log2-m* 1), A ?l ?k) (elementos-derecha P ?l ?k)) ;r10lk
                      (regla-comunicacion (etiqueta-izquierda 2) (etiqueta-derecha 0)
                                          (elementos-izquierda P ?l ?k) (elementos-derecha R ?l ?k , PC ?l ?k))               ;r11lk
                      (regla-comunicacion (etiqueta-izquierda 2) (etiqueta-derecha 0)
                                          (elementos-izquierda PC ?l ?k) (elementos-derecha B ?l ?k , G ?l ?k))               ;r12lk
                      (regla-comunicacion (etiqueta-izquierda 2) (etiqueta-derecha 0)
                                          (elementos-izquierda R ?l , R ?l ?k) (elementos-derecha R ?l , RC ?k))              ;r13lk
                      (regla-comunicacion (etiqueta-izquierda 2) (etiqueta-derecha 0)
                                          (elementos-izquierda B ?l , B ?l ?k) (elementos-derecha B ?l , BC ?k))              ;r14lk
                      (regla-comunicacion (etiqueta-izquierda 2) (etiqueta-derecha 0)
                                          (elementos-izquierda G ?l , G ?l ?k) (elementos-derecha G ?l , GC ?k)))             ;r15lk

              (bind ?l (+ ?l 1))))

    (if (<= ?k ?*techo-log2-m*)     ;k = 1 ... [log2(m)]
      then (assert (regla-comunicacion (etiqueta-izquierda 2) (etiqueta-derecha 0)
                                       (elementos-izquierda d ?k) (elementos-derecha d (+ ?k 1) , d (+ ?k 1)))))  ;r7k

    (if (and (>= ?k 2) (<= ?k (+ ?*techo-log2-m* 6))) ;k = 2 ... [log2(m)] + 6
      then (assert (regla-comunicacion (etiqueta-izquierda 2) (etiqueta-derecha 0)
                                       (elementos-izquierda f ?k) (elementos-derecha f (+ ?k 1)))))               ;r9k

    (bind ?k (+ ?k 1))) ;Incremento para el bucle y fin de bucle.

  (assert (regla-comunicacion (etiqueta-izquierda 2) (etiqueta-derecha 0)
                              (elementos-izquierda c (+ (* 2 ?*n-vertices*) 1)) (elementos-derecha d 1 , E))  ;r6
          (regla-comunicacion (etiqueta-izquierda 2) (etiqueta-derecha 0)
                              (elementos-izquierda f (+ ?*techo-log2-m* 7) , e) (elementos-derecha T))        ;r20

          ;REGLAS DE COMUNICACION (1 <-> 2)
          (regla-comunicacion (etiqueta-izquierda 1) (etiqueta-derecha 2)
                              (elementos-izquierda c (+ (* 2 ?*n-vertices*) 1)) (elementos-derecha D)))       ;r5

)

;DIVISION
(defrule division "crea dos nuevas membranas en sustitucion de una existente y a partir de una regla de division concreta"
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
(defrule comunicacion "intercambia ciertos elementos de dos membranas a partir una regla de comunicacion concreta"
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

;DATOS INICIALES

(deffacts tp-system "especificacion del sistema P basado en tejidos con division celular para el problema 3-COL"

  ;MEMBRANAS
  ;La membrana 0 representa al entorno (salida) y requiere ser inicializada con datos de una instancia concreta del problema.
  ; Ademas contiene el resto de elementos necesarios para el sistema. [0 - {yes, no}]
  (membrana (etiqueta 0)
            (contenido , b , D , S , N ,)) ;Constantes presentes para cualquier instancia del problema.

  (membrana (etiqueta 1) ;El estado inicial de la membrana 1 es igual para cualquier instancia del problema.
            (contenido , a 1 , b , c 1 , yes , no ,))

  ;La membrana 2 contiene, entre otros, los elementos de entrada que representan una instancia del problema,
  ; por tanto tambien requiere ser inicializada.
  (membrana (etiqueta 2)
            (contenido , D ,))

  ;REGLAS
  ;Las reglas incluidas en esta seccion son iguales para cualquier instancia.

  ;REGLAS DE COMUNICACION (2 <-> 0)
  (regla-comunicacion (etiqueta-izquierda 2) (etiqueta-derecha 0) (elementos-izquierda E) (elementos-derecha e , f 2))  ;r8
  (regla-comunicacion (etiqueta-izquierda 2) (etiqueta-derecha 0) (elementos-izquierda e , z) (elementos-derecha))      ;r19

  ;REGLAS DE COMUNICACION (2 <-> 1)
  (regla-comunicacion (etiqueta-izquierda 2) (etiqueta-derecha 1) (elementos-izquierda T) (elementos-derecha))          ;r21

  ;REGLAS DE COMUNICACION (1 <-> 0)
  (regla-comunicacion (etiqueta-izquierda 1) (etiqueta-derecha 0) (elementos-izquierda b , T) (elementos-derecha S))    ;r22
  (regla-comunicacion (etiqueta-izquierda 1) (etiqueta-derecha 0) (elementos-izquierda S , yes) (elementos-derecha))    ;r23
  (regla-comunicacion (etiqueta-izquierda 1) (etiqueta-derecha 0) (elementos-izquierda N no) (elementos-derecha))       ;r25

)

(deffacts ejemplo1-instancia-3-col "datos de ejemplo de un problema 3-COL"
  ()
)

(deffacts ejemplo2-instancia-3-col "datos de ejemplo de un problema 3-COL"
  ()
)
