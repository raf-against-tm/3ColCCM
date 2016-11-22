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

(defclass CONSTANTE (is-a USER)
  (slot simbolo (propagation no-inherit))
  (slot copias  (propagation no-inherit))
)

(defclass CONTADOR (is-a USER)
  (slot simbolo (propagation no-inherit))
  (slot valor   (propagation no-inherit))
  (slot copias  (propagation no-inherit))
)

(defclass VERTICE (is-a USER) ;1 <= indice <= n
  (slot color   (propagation no-inherit))
  (slot indice  (propagation no-inherit))
)

(defclass ARISTA (is-a VERTICE) ;1 <= vertice-i < vertice-j <= n
  (slot color     (propagation no-inherit))
  (slot vertice-i (propagation no-inherit))
  (slot vertice-j (propagation no-inherit))
)

(defclass CELULA (is-a CONSTANTE CONTADOR ARISTA VERTICE)
  (slot etiqueta        (propagation no-inherit))
  (multislot constantes (propagation no-inherit))
  (multislot contadores (propagation no-inherit))
  (multislot vertices   (propagation no-inherit))
  (multislot aristas    (propagation no-inherit))
)

;FUNCIONES AUXILIARES

(deffunction techo (?valor)
  (if (> ?valor (integer ?valor)) then (+ (integer ?valor) 1) else (integer ?valor))
)

;REGLAS DE INICIALIZACION

;TODO CREAR REGLA PARA GENERAR LOS CONTADORES Y SUS VALORES INICIALES Y FINALES

;REGLAS DE DIVISION CELULAR

;TODO

;REGLAS DE COMUNICACION ENTRE CELULAS

;TODO

;DATOS INICIALES (CODIFICACION DE LA INSTANCIA DEL PROBLEMA 3-COL)

;TODO CONJUNTO INICIAL DE PRUEBA GRAFO DE 3 VERTICES 3 ARISTAS

(definstances VERTICES
  (A1 of VERTICE (color A) (indice 1))
  (A2 of VERTICE (color A) (indice 2))
  (A3 of VERTICE (color A) (indice 3))
)

(definstances ARISTAS
  (A12 of ARISTA (color A) (vertice-i [A1]) (vertice-j [A2]))
  (A13 of ARISTA (color A) (vertice-i [A1]) (vertice-j [A3]))
  (A23 of ARISTA (color A) (vertice-i [A2]) (vertice-j [A3]))
)

(definstances CELULAS
  (C0 of CELULA (etiqueta 0) ;Celula que representa al entorno
                (constantes b D E e T S N bb)
                (vertices   [A1] [A2] [A3])
                (aristas    [A12] [A13] [A23]))

  (C1 of CELULA (etiqueta 1)
                (constantes b yes no))

  (C2 of CELULA (etiqueta 2) ;Celula con datos de entrada
                (constantes D)
                (vertices   [A1] [A2] [A3])
                (aristas    [A12] [A13] [A23]))

)
