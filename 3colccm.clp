;SOLUCION PARA EL PROBLEMA 3-COL MEDIANTE COMPUTACION CELULAR CON MEMBRANAS.

;RAFAEL VALLE MORALES. INGENIERIA INFORMATICA (PLAN 97)

;[ARCHIVO SIN TILDES]

;El problema 3-COL consiste en determinar si un mapa puede ser coloreado unicamente con 3 colores, teniendo
; en cuenta que las regiones contiguas deben tener colores distintos. Toda instancia del problema es codificada
; por un grafo cuyos vertices determinan las distintas regiones del mapa, y cuyas aristas definen la contiguidad de
; dichas regiones. De manera que, los datos de entrada del sistema seran los elementos (vertices y aristas) del grafo
; correspondiente al mapa sobre el que se desea obtener una respuesta.

;TODO BREVE EXPLICACION DEL MODELO DE COMPUTACION CELULAR CON MEMRANAS BASADO EN TEJIDOS
;TODO BREVE EXPLICACION DEL SISTEMA IMPLEMENTADO
;TODO BIBLIOGRAFIA.


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

(deftemplate instancia-3col ;Define una instancia del problema 3-COL codifcado por su grafo asociado.
  (slot n-vertices)
  (multislot vertices) ;(vertices , A 1 , A 2 , ... , An ,)
  (slot m-aristas)
  (multislot aristas)  ;(aristas , A 1 2 , A 1 3 , ... , A i j ,) con [1 <= i < j <= n]
)

;FUNCIONES AUXILIARES

(deffunction techo (?valor)
  (if (> ?valor (integer ?valor)) then (+ (integer ?valor) 1) else (integer ?valor))
)

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

  (bind ?log2-m (/ (log ?m-aristas) (log 2)))
  (bind ?techo-log2-m (techo ?log2-m))

  (assert (inicializa-vertices ?n-vertices $?vertices)    ;(A 1 , A 2 , ... , A n)
          (inicializa-aristas ?m-aristas $?aristas)       ;(A 1 2 , A 1 3 , ... , A i j) con 1 <= i < j <= n
          (inicializa-contadores a (+ (*  2 ?n-vertices) ?techo-log2-m 12) 1) ; 1 ... 2n + [log2(m)] + 12. 1 copia de cada elemento contador.
          (inicializa-contadores c (+ (* 2 ?n-vertices) 1) (integer (** 4  ?n-vertices))) ; 1 ... 2n + 1. 4 elevado a n copias.
          (inicializa-contadores d (+ ?techo-log2-m 1) (integer (** 2  ?techo-log2-m)))   ; 1 ... [log2(m)] + 1. 2 elevado a [log2(m)] copias.
          (inicializa-contadores f (+ ?techo-log2-m 7) 1))  ; 1 ... [log2(m)] + 7. 1 copia de cada elemento contador

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
  (modify ?membrana0 (contenido $?c0 A ?i ?j , P ?i ?j , PC ?i ?j , R ?i ?j , B ?i ?j , G ?i ?j ,))
  (modify ?membrana2 (contenido $?c2 A ?i ?j ,))
  (retract ?ia)

  (if (neq ?m-aristas 1) then (retract ?ia) (assert (inicializa-aristas (- ?m-aristas 1) $?ai , $?af)))


)

(defrule inicializacion-contadores "genera los contadores necesarios en el entorno"

  ?ic <- (inicializa-contadores ?tipo ?n-contadores ?m-copias)

  ?membrana0 <- (membrana (etiqueta 0) ;Entorno
                          (contenido $?c0))

  =>
  (modify ?membrana0 (contenido $?c0 ?tipo ?n-contadores ,))
  (retract ?ic)

  (if (> ?m-copias 1)   ;Si el numero de copias no es 1 estamos en los casos de los contadores c y d.
    then (assert (inicializa-contadores ?tipo ?n-contadores (- ?m-copias 1)))

    else (if (eq ?tipo f) ;Caso del contador f.
           then (if (> ?n-contadores 2)
                  then (assert (inicializa-contadores f (- ?n-contadores 1) 1)))

           else (if (> ?n-contadores 1) ;Casos de los contadores a, c y d con todas las copias del contador i generadas.
                  then (bind ?n-contadores (- ?n-contadores 1))
                       (switch ?tipo
                         (case a then (assert (inicializa-contadores ?tipo ?n-contadores ?m-copias)))
                         (case c then (assert (inicializa-contadores ?tipo ?n-contadores (integer (** 2 (- ?n-contadores 1))))))
                         (case d then (assert (inicializa-contadores ?tipo ?n-contadores (integer (** 2 (- ?n-contadores 1))))))))))

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
            (contenido , b , D , E , e , T , S , N , bb ,)) ;Constantes presentes en todos las instancias.

  (membrana (etiqueta 1) ;La membrana 1 es igual para todas las instancias del problema.
            (contenido , a 1 , b , c 1 , yes , no ,))

  ;La membrana 2 contiene, entre otros, los elementos de entrada que representan una instancia del problema, requiere ser inicializada.
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
