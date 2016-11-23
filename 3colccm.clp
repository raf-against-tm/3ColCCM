;SOLUCION PARA EL PROBLEMA 3-COL MEDIANTE COMPUTACION CELULAR CON MEMBRANAS.

;RAFAEL VALLE MORALES. INGENIERIA INFORMATICA (PLAN 97)

;El problema 3-COL consiste en determinar si un mapa puede ser coloreado unicamente con 3 colores, teniendo
; en cuenta que las regiones contiguas deben tener colores distintos.

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

;TODO Usar assert para introducir los parametros necesarios e independientemente del codigo o dentro del codigo?¿

;ESTRUCTURAS DE DATOS

(deftemplate membrana
  (slot etiqueta)
  (multislot contenido)
)

(deftemplate regla-division
  (slot etiqueta)
  (multislot elemento-izquierda)
  (multislot elemento-derecha1)
  (multislot elemento-derecha2)
)

(deftemplate regla-comunicacion
  (slot etiqueta-izquierda)
  (slot etiqueta-derecha)
  (multislot elementos-izquierda)
  (multislot elementos-derecha)
)

;FUNCIONES AUXILIARES

(deffunction techo (?valor)
  (if (> ?valor (integer ?valor)) then (+ (integer ?valor) 1) else (integer ?valor))
)

;REGLAS

(defrule inicializa ;MODIFICAR PARA NUEVA IMPLEMENTACION
  ?inif <- (initial-fact)
  =>
  (retract ?inif)
  (bind ?n (length (send [C0] get-vertices)))
  (bind ?m (length (send [C0] get-aristas)))
  (bind ?i 1)
  (while (<= ?i (+ (techo (/ (log ?m) (log 2))) 12)) ;Genera instancias del contador a
         (send [C0] put-contadores (make-instance (sym-cat a ?i) of CONTADOR (simbolo a) (valor ?i))
                                   (send [C0] get-contadores))
         (bind ?i (+ ?i 1)))

  (bind ?i 1)
  (while (<= ?i (+ (techo (/ (log ?m) (log 2))) 12)) ;Genera instancias del contador
         (send [C0] put-contadores (make-instance (sym-cat a ?i) of CONTADOR (simbolo a) (valor ?i))
                                   (send [C0] get-contadores))
         (bind ?i (+ ?i 1)))

)

;TODO Implementar regla de inicializacion para generar todas las reglas y elementos dependientes de los parametros n y m

;TODO Implementar regla para mostrar el resultado final a partir de la entrada dada

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

;DATOS INICIALES

;TODO Implementar 2 ejemplos

(deffacts recognizer-tp-system

  ;MEMBRANAS
  (membrana (etiqueta 0) ;Membrana que representa al entorno (salida)
            (contenido , a 1 , a 2 , a 3 , a 4 , a 5 , a 6 ,))

  (membrana (etiqueta 1)
            (contenido , a 1 , b , c 1 , yes , no ,))

  (membrana (etiqueta 2) ;Membrana con datos de entrada
            (contenido , D , A 1 , A 2 , A 3 , A 1 2 , A 1 3 , A 2 3 ,))

  ;REGLAS DE DIVISION
  ;(regla-division (etiqueta 2) (elemento-izquierda A i) (elemento-derecha1 R i) (elemento-derecha2 T i)) ;r1i
  ;(regla-division (etiqueta 2) (elemento-izquierda T i) (elemento-derecha1 B i) (elemento-derecha2 G i)) ;r2i

  ;Instancias de las reglas de division
  (regla-division (etiqueta 2) (elemento-izquierda A 1) (elemento-derecha1 R 1) (elemento-derecha2 T 1)) ;R11
  (regla-division (etiqueta 2) (elemento-izquierda A 2) (elemento-derecha1 R 2) (elemento-derecha2 T 2)) ;R12
  (regla-division (etiqueta 2) (elemento-izquierda A 3) (elemento-derecha1 R 3) (elemento-derecha2 T 3)) ;R13
  (regla-division (etiqueta 2) (elemento-izquierda T 1) (elemento-derecha1 B 1) (elemento-derecha2 G 1)) ;R21
  (regla-division (etiqueta 2) (elemento-izquierda T 2) (elemento-derecha1 B 2) (elemento-derecha2 G 2)) ;R22
  (regla-division (etiqueta 2) (elemento-izquierda T 3) (elemento-derecha1 B 3) (elemento-derecha2 G 3)) ;R23

  ;REGLAS DE COMUNICACION
  (regla-comunicacion (etiqueta-izquierda 1) (etiqueta-derecha 0) (elementos-izquierdos a i) (elementos-derechos a i+1))                ;r3i
  (regla-comunicacion (etiqueta-izquierda 1) (etiqueta-derecha 0) (elementos-izquierdos c i) (elementos-derechos c i+1 , c i+1))        ;r4i

  (regla-comunicacion (etiqueta-izquierda 1) (etiqueta-derecha 2) (elementos-izquierdos c 2n+1) (elementos-derechos D))                 ;r5

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

  (regla-comunicacion (etiqueta-izquierda 2) (etiqueta-derecha 1) (elementos-izquierdos T) (elementos-derechos))                        ;r21

  (regla-comunicacion (etiqueta-izquierda 1) (etiqueta-derecha 0) (elementos-izquierdos b , T) (elementos-derechos S))                  ;r22
  (regla-comunicacion (etiqueta-izquierda 1) (etiqueta-derecha 0) (elementos-izquierdos S , yes) (elementos-derechos))                  ;r23
  (regla-comunicacion (etiqueta-izquierda 1) (etiqueta-derecha 0) (elementos-izquierdos a 2n+tlog2m+12 , b) (elementos-derechos N))     ;r24
  (regla-comunicacion (etiqueta-izquierda 1) (etiqueta-derecha 0) (elementos-izquierdos N no) (elementos-derechos))                     ;r25

  ;(regla-comunicacion (etiqueta-izquierda 1) (etiqueta-derecha 0) (elementos-izquierda a 1) (elementos-derecha a 2))


)
