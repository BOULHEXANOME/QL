open util/integer

/***************************************
										Let
***************************************/

let DCAP = 5
let RCAP = 10


/***************************************
										Sig
***************************************/

some sig Drone {
	position: one Intersection,
	commande: lone Commande,
	batterie: Int,
	chemin : seq Receptacle
}

one sig Temps {
	tempsActuel:Int
}

some sig Receptacle {
	position: one Intersection,
	distances : seq Int,
	listeRecep : seq Receptacle,
	contenu : Int
}

one sig Entrepot {
	position: one Intersection,
	ensembleCommandes: set Commande
}

sig EnsembleProduits {
	contenu: Int
}

some sig Commande {
	destination: one Receptacle,
	ensembleProd: lone EnsembleProduits // On permet de créer une commande pour aller à l'entrepot, sans ensembleProd pour gérer le retour du drone
}

sig Intersection {
	X : Int,
	Y : Int
}


/***************************************
										Fact
***************************************/

// la batterie du drone est entre 0 et 3
fact BatterieDrone {
	all d:Drone | d.batterie >= 0 && d.batterie <= 3
}

// les drones ont une capacité max de DCAP
fact CapaciteDrone {
	all d: Drone | d.commande.ensembleProd.contenu <= DCAP && d.commande.ensembleProd.contenu > 0
}

// les réceptacles ont une capacité max de RCAP
fact CapaciteReceptacle {
	all r: Receptacle | r.contenu <= RCAP
}


// Ensemble de Produits appartient à une commande
fact EnsembleProdDansCommande {
	all e:EnsembleProduits | some c:Commande | c.ensembleProd = e
}

// L'entrepôt a une liste de toutes les commandes
fact EntrepotListeCommande {
	all c:Commande | some e:Entrepot | c in e.ensembleCommandes
}

// Si la commande contient un ensemble de prod, alors elle ne peut pas être livrée à l'entrepôt
fact PasLivraisonEntrepot {
	all c:Commande | one c.ensembleProd => c.destination.position != Entrepot.position
}

// Il y a au moins un receptacle sur une intersection voisine de l'entrepot
fact EntrepotAUnVoisin {
	some r:Receptacle | 
	((r.position.X = Entrepot.position.X.add[1] || r.position.X = Entrepot.position.X.sub[1]) && (r.position.Y = Entrepot.position.Y))
	||
	((r.position.X = Entrepot.position.X) && (r.position.Y = Entrepot.position.Y.add[1] || r.position.Y = Entrepot.position.Y.sub[1]))
}


// Il n'existe pas 2 intersectiones identiques
fact IntersectionUnitaire {
	all disj i1,i2: Intersection | i1.X != i2.X || i1.Y != i2.Y
}

// Il n'existe pas des intersections avec 2 receptacles
fact ReceptacleUnitaire {
	all disj r1,r2: Receptacle |
	not (r1.position=r2.position)
}

// aucun réceptacle ne peut partager son intersection avec l'entrepôt
fact EntrepotPasSurReceptacle {
	all r: Receptacle | not (Entrepot.position = r.position)
}

// taille de la grille
fact LimitationPositions {
	all i:Intersection | i.X <=6 && i.X >= 0 && i.Y <= 6 && i.Y >= 0
}

fact NonLuiMeme {
	all r:Receptacle | r not in r.listeRecep.elems
}

fact ListeReceptacle {
	all r1:Receptacle | some r2:Receptacle | distance[r1.position, r2.position] < 4 && distance[r1.position, r2.position]>0 =>
	r2 in elems[r1.listeRecep]
	all r1:Receptacle | some r2:Receptacle | distance[r1.position,r2.position] in elems[r1.distances]	
	//r1.listeRecep = r1.listeRecep.add[r2] 
}

/*
// détermination du nombre d'instances
fact NombreInstances {
	#Drone <= 3
	#Receptacle <= 3
	#EnsembleProduits <= 3
	#Commande <= 3
	#Intersection <= 8
}*/


/***************************************
										Pred
***************************************/

pred initialiser {
	all d:Drone | d.batterie = 3
}

pred remplirListeReceptaclesAccessibles {
}


/***************************************
										Fun
***************************************/

// calcule la valeur absolue
fun abs[x: Int] : Int {
	(x<0) => x.mul[-1] else (x)
}

// calcule la distance entre deux intersections
fun distance[i1,i2: Intersection]: Int {
//    abs[abs[i1.X.sub[i2.X]].add[abs[i1.Y.sub[i2.Y]]]]
	i1.X.sub[i2.X].add[i1.Y.sub[i2.Y]]
}
 
/***************************************
										Run
***************************************/

run initialiser for 1 Drone, exactly 3 Receptacle, 1 EnsembleProduits, 1 Commande, 5 Intersection, 6 int

/***************************************
										Assert
***************************************/



/***************************************
										Check
***************************************/


