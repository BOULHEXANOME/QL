open util/integer
open util/ordering[Temps]

/***************************************
										Let
***************************************/

let DCAP = 5
let RCAP = 10


/***************************************
										Sig
***************************************/

some sig Drone {
	position: Intersection one -> Temps,
	commande: lone Commande,
	batterie: Int one->Temps,
	chemin : seq Receptacle -> Temps
}

sig Temps {}

some sig Receptacle {
	position: one Intersection,
	distances : seq Int,
	listeRecep : seq Receptacle,
	contenu : Int one -> Temps
}

one sig Entrepot {
	position: one Intersection,
	ensembleCommandes: set Commande
}

sig EnsembleProduits {
	contenu: Int
}

some sig Commande {
	destination: Receptacle one-> Temps,
	ensembleProd: EnsembleProduits lone-> Temps// On permet de créer une commande pour aller à l'entrepot, sans ensembleProd pour gérer le retour du drone
}

sig Intersection {
	X : Int,
	Y : Int
}


/***************************************
										Fact
***************************************/

// la batterie du drone est entre 0 et 3
fact DroneContraintes {
	all d:Drone, t:Temps | d.batterie.t >= 0 && d.batterie.t < 4 //Bornes de la batterie
	all d: Drone, t:Temps | d.commande.ensembleProd.t.contenu <= DCAP && d.commande.ensembleProd.t.contenu > 0
	
}

// les réceptacles ont une capacité max de RCAP
fact CapaciteReceptacle {
	all r: Receptacle, t:Temps | r.contenu.t <= RCAP && r.contenu.t >= 0
}


// Ensemble de Produits appartient à une commande
fact EnsembleProdDansCommande {
	all e:EnsembleProduits, t:Temps | some c:Commande | c.ensembleProd.t = e
}

// L'entrepôt a une liste de toutes les commandes
fact EntrepotListeCommande {
	all c:Commande | some e:Entrepot | c in e.ensembleCommandes
}

// Si la commande contient un ensemble de prod, alors elle ne peut pas être livrée à l'entrepôt
fact PasLivraisonEntrepot {
	all c:Commande,t:Temps| one c.ensembleProd => c.destination.t.position != Entrepot.position
}

// Il y a au moins un receptacle sur une intersection voisine de l'entrepot
fact EntrepotAUnVoisin {
	some r:Receptacle | distance[r.position, Entrepot.position] = 1
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
	all d:Drone | d.batterie.first = 3
	all d:Drone | d.position.first = Entrepot.position
	all c:Commande | c.destination.first.position = Entrepot.position
	
	all c:Commande | c.ensembleProd.first.contenu > 0
	all d:Drone | no r:seq Receptacle |d.chemin.first = r

}

pred remplirListeReceptaclesAccessibles {
}

pred intersectionVide[t,t':Temps, d':Drone, i:Intersection] {
	i = Entrepot.position //L'entrepôt est toujours disponible
	||
	all d:Drone - d'| d.position.t' != i
}

pred go {

	initialiser
	all t:Temps - last |let t'=t.next |
	{
		all d:Drone | moveDrone[t,t',d]
	}
}

pred moveDrone[t,t':Temps, d:Drone]{

	//majBatterie
	/*d.position.t' = d.position.t && some r:Receptacle | d.position.t = r.position => d.batterie.t' = d.batterie.t.add[1] else
	d.position.t' = d.position.t => d.batterie.t' = d.batterie.t else//immobile
	d.position.t' != d.position.t => d.batterie.t' = d.batterie.t.sub[1] //mouvement
	*/
	
	d.position.t = d.commande.destination.t.position => {//Le drone est a destination


		d.position.t = Entrepot.position => { //entrepot destination
			
		} else { // réceptacle destination
			d.commande.destination.t.contenu.t' = (d.commande.destination.t.contenu.t+d.commande.ensembleProd.t)//Le réceptacle change sa capacité
			d.commande.ensembleProd.t.contenu = 0
			d.commande.destination.t'.position = Entrepot.position
			d.position.t' = d.position.t => d.batterie.t' = d.batterie.t//immobile
		}
	}else{//Le drone n'est pas à destination
			intersectionVide[t,t',d,d.chemin.t.first.position] => { //Si on peut bouger, on le fait
			d.position.t' = d.chemin.t.first.position//on déplace le drone
			d.position.t' != d.position.t => d.batterie.t' = d.batterie.t.sub[1] //mouvement
		}
	}
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

check fin for 1 Drone, exactly 1 Receptacle, 1 EnsembleProduits, 1 Commande, 2 Intersection, 6 int, 10 Temps

/***************************************
										Assert
***************************************/

assert positive {
	no x:Int | x.abs < 0
	all i1:Intersection | no i2:Intersection |i1.distance[i2] < 0
}

assert fin {
	some t:Temps | all d:Drone | {
		d.position.t = Entrepot.position
		d.commande.destination.t.position = Entrepot.position
	}
}



/***************************************
										Check
***************************************/
check positive

