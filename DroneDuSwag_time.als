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
	commande: one Commande,
	batterie: Int one->Temps,
	chemin : seq Receptacle->Temps
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
}


some sig Commande {
	destination: Receptacle one->Temps,
	contenu: Int one->Temps// On permet de créer une commande pour aller à l'entrepot, sans ensembleProd pour gérer le retour du drone
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
	all d: Drone, t:Temps | d.commande.contenu.t<= DCAP && d.commande.contenu.t>= 0
}

// les réceptacles ont une capacité max de RCAP
fact CapaciteReceptacle {
	all r: Receptacle, t:Temps | r.contenu.t <= RCAP && r.contenu.t >= 0
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
	all i:Intersection | i.X <=9 && i.X >= 0 && i.Y <= 9 && i.Y >= 0
}

fact NonLuiMeme {
	all r:Receptacle | r not in r.listeRecep.elems
}

// Remplissage liste des receptacles accessibles
fact ListeReceptacleAuMoins1Accessible {
	all r1:Receptacle | some r2:Receptacle | 	r2 in elems[r1.listeRecep] && r1 in elems[r2.listeRecep]
}
fact ListeReceptacleContraintesDistance{
	no r1:Receptacle | some r3:Receptacle | (distance[r1.position, r3.position] > 3 || distance[r1.position, r3.position]<=0) &&
	r3 in elems[r1.listeRecep]
}
fact ListeReceptacleAjoutTousAccessibles{
	all r1:Receptacle | all r2:Receptacle | (distance[r1.position, r2.position] < 4 && distance[r1.position, r2.position]>0) =>
	(r2 in elems[r1.listeRecep] && r1 in elems[r2.listeRecep])
}
fact ListeReceptacleSansDoublons{
	all r1:Receptacle | ! hasDups[r1.listeRecep]
}

fact CheminSansDoublons{
//	all d: Drone | ! hasDups[d.chemin]
	all d: Drone, t:Temps | # elems[d.chemin.t] = # inds[d.chemin.t]
}

fact PremierDuChemin{
	all d:Drone, t:Temps | some r: Receptacle | !d.chemin.t.isEmpty => (first[d.chemin.t]= r && distance[Entrepot.position, r.position] <= 3)
}
fact DernierDuChemin{
	all d:Drone, t:Temps | !d.chemin.t.isEmpty => (last[d.chemin.t]= d.commande.destination.t)
}
fact CommandeUnSeulDrone{
	all disj d,d2:Drone | d.commande != d2.commande
}

fact {go}

/***************************************
										Pred
***************************************/

pred initialiser {
	all d:Drone | {
		d.batterie.first = 3
		d.position.first = Entrepot.position
		d.commande.contenu.first = 0
		d.chemin.first.isEmpty
	}
}

pred intersectionVide[t,t':Temps, d':Drone, i:Intersection] {
	i = Entrepot.position //L'entrepôt est toujours disponible
	||
	all d:Drone - d'| d.position.t' != i
}

pred calculerChemin[d:Drone] {
	all r : Receptacle | r in d.chemin.first.elems && last[d.chemin.first] != r //est pas dernier elem
		=> r in d.chemin.first[idxOf[d.chemin.first,r]+1].listeRecep.elems
}

pred go {
	initialiser
	all t:Temps - last |let t'=t.next |
	{
		all d:Drone | moveDrone[t,t',d]
	}
}

pred moveDrone[t,t':Temps, d:Drone]{

	d.batterie.t' = d.batterie.t
	d.position.t' = d.position.t
	d.chemin.t' = d.chemin.t
	
	//majBatterie
	/*d.position.t' = d.position.t && some r:Receptacle | d.position.t = r.position => d.batterie.t' = d.batterie.t.add[1] else
	d.position.t' = d.position.t => d.batterie.t' = d.batterie.t else//immobile
	d.position.t' != d.position.t => d.batterie.t' = d.batterie.t.sub[1] //mouvement
	*/
	/*
	d.position.t = d.commande.destination.position => {//Le drone est a destination
		d.position.t = Entrepot.position => { //entrepot destination
			
		} else { // réceptacle destination
			d.commande.destination.contenu.t' = (d.commande.destination.contenu.t+d.commande.ensembleProd.t)//Le réceptacle change sa capacité
			d.commande.ensembleProd.t.contenu = 0
			d.position.t' = d.position.t => d.batterie.t' = d.batterie.t//immobile
		}
	}else{//Le drone n'est pas à destination
		intersectionVide[t,t',d,d.chemin.first.position] => { //Si on peut bouger, on le fait
		d.position.t' = d.chemin.first.position//on déplace le drone
		d.position.t' != d.position.t => d.batterie.t' = d.batterie.t.sub[1] //mouvement
		}
	}*/

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
run go for 1 Drone, exactly 2 Receptacle, 1 Commande,  4 Intersection, 7 int, 10 Temps

/***************************************
										Assert
***************************************/

assert positive {
	no x:Int | x.abs < 0
	all i1:Intersection | no i2:Intersection |i1.distance[i2] < 0
}

/*assert fin {
	some t:Temps | all d:Drone, c:Commande | {
		d.position.t = Entrepot.position
		c.contenu.t = 5
	}
}*/



/***************************************
										Check
***************************************/
check positive
