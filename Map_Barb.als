open util/integer
open util/boolean

sig coord {
	x:Int,
	y:Int
}

sig intersection {libre:Bool}

sig Map {values: coord  -> lone intersection}

assert mappingIsUnique {
	all m:Map,    c:coord, v, v':intersection |
						c -> v in m.values and
						c -> v' in m.values
						implies v = v'
} 

assert numberOfIntersections {
	all c:coord |  c.x <= 2 && c.y <= 2
	
}

fact {
			all c:coord | some f:intersection, m:Map | c -> f in m.values
			all f:intersection | some c:coord, m:Map | c -> f in m.values
}

check numberOfIntersections for 4
