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

abstract sig PositionCible{
	listeRecep : seq Receptacle,
	position: one Intersection
}

some sig Receptacle extends PositionCible{
	contenu : Int one->Temps
}

one sig Entrepot extends PositionCible{
	ensembleCommandes: set Commande -> Temps
}


some sig Commande {
	destination: PositionCible one -> Temps,
	contenu: Int one->Temps // On permet de créer une commande pour aller à l'entrepot, sans ensembleProd pour gérer le retour du drone
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
}

fact LimitesCommandes {
	all c:Commande, t:Temps | c.contenu.t<= DCAP && c.contenu.t>= 0
}

fact CommandesPasSurReceptacle {
	all c:Commande, t:Temps | c.contenu.t > 0 => c.destination.t != Entrepot
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

fact {go}

fact TestCheminPlusLong{
	all d: Drone | # inds[d.chemin] > 3
}
fact testSurCheminHS{
	all r : Receptacle| all d : Drone |
		/*last[d.chemin] != r && */
		r in d.chemin[idxOf[d.chemin,r]+1].listeRecep.elems
		=> r in d.chemin.elems
}

/***************************************
										Pred
***************************************/

pred initialiser {

	all d:Drone | d.batterie = 3
//	all d:Drone | calculerChemin[d]
}

/*pred calculerChemin[d:Drone] {
	all r : Receptacle |
		last[d.chemin] != r && 
		r in d.chemin[idxOf[d.chemin,r]+1].listeRecep.elems
		=> r in d.chemin.elems
		
}*/
pred go {
	initialiser
	all t:Temps - last |let t'=t.next |
	{
		all d:Drone | bougerDrone[t,t',d]
		/*all c:Commande | c in Entrepot.ensembleCommandes.t => c.contenu.t'=c.contenu.t && c.destination.t'=c.destination.t
		Entrepot.ensembleCommandes.t'=Entrepot.ensembleCommandes.t*/
	}
}

pred intersectionVide[t,t':Temps, d:Drone, i:Intersection]{
	
	

}

pred bougerDrone[t,t':Temps, d:Drone]{
	
	//majBatterie
	/*d.position.t' = d.position.t && some r:Receptacle | d.position.t = r.position => d.batterie.t' = d.batterie.t.add[1] else
	d.position.t' = d.position.t => d.batterie.t' = d.batterie.t else//immobile
	d.position.t' != d.position.t => d.batterie.t' = d.batterie.t.sub[1] //mouvement
	*/
	
	// la commande du drone est vide et le drone et à l'entrepot et il reste des commandes à livrer non vide
	some c:Commande | (c in Entrepot.ensembleCommandes.t && c.contenu.t > 0 && d.commande.contenu.t = 0 && d.position.t = Entrepot.position)
		=> (d.commande.destination.t' = c.destination.t && d.commande.contenu.t' = c.contenu.t)
	
	d.commande.contenu.t !=0 => deplacerDrone[d,t,t']
	
	d.commande.contenu.t!=0 && d.position.t = d.commande.destination.t.position => dechargementCommande[d,t,t']

	
	
	/*d.commande.contenu.t = 0 => {//Le contenu est vide
		d.position.t = Entrepot.position => { //entrepot
			one c:Commande | c in Entrepot.ensembleCommandes.t => {//il reste des commandes
				d.commande.destination.t' = c.destination.t
				d.commande.contenu.t' = c.contenu.t
				d.batterie.t'=d.batterie.t
				d.position.t'=d.position.t
				d.calculerChemin[t']
			} else {
				d.commande.destination.t' = d.commande.destination.t
				d.commande.contenu.t' = d.commande.contenu.t
				d.batterie.t'=d.batterie.t
				d.position.t'=d.position.t
				d.chemin.t' = d.chemin.t
			}
		} else { // réceptacle destination
				d.commande.destination.t' = d.commande.destination.t
				d.commande.contenu.t' = d.commande.contenu.t
				d.batterie.t'=d.batterie.t
				d.position.t'=d.position.t
				d.chemin.t' = d.chemin.t
		}
	}else{//Le drone n'est pas à destination
				d.commande.destination.t' = d.commande.destination.t
				d.commande.contenu.t' = d.commande.contenu.t
				d.batterie.t'=d.batterie.t
				d.chemin.t' = d.chemin.t
				d.position.t'=d.chemin.t.first.position
				d.batterie.t' = d.batterie.t.sub[1]
	}*/
}

pred deplacerDrone[d:Drone,t,t':Temps]{
	
	d.position.t' = d.chemin.t[d.chemin.t.idxOf[d.position.t]+1].position
	d.batterie.t'=d.batterie.t.sub[1]
	d.chemin.t' = d.chemin.t
	d.commande.destination.t' = d.commande.destination.t
	d.commande.contenu.t' = d.commande.contenu.t

	all r:Receptacle | r.contenu.t' = r.contenu.t

}

pred dechargementCommande[d:Drone, t,t':Temps]{
	d.position.t' = d.position.t
	d.batterie.t' = d.batterie.t
	d.chemin.t'=d.chemin.t	
	d.commande.destination.t.contenu.t'=d.commande.destination.t.contenu.t.add[d.commande.contenu.t]
	d.commande.contenu.t' = 0
	d.commande.destination.t' = d.commande.destination.t
	all r:Receptacle-d.commande.destination.t | r.contenu.t' = r.contenu.t
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
    abs[abs[i1.X.sub[i2.X]].add[abs[i1.Y.sub[i2.Y]]]]
}

/***************************************
										Run
***************************************/

run initialiser for exactly 1 Drone, exactly 6 Receptacle, 1 EnsembleProduits, exactly 1 Commande, 15 Intersection, 6 int, 17 PositionCible

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
		c.contenu.t = 0
	}
}*/


/***************************************
										Check
***************************************/

check positive
