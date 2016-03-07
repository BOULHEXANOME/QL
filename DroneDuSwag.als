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
	contenu : Int
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
	all r: Receptacle | r.contenu <= RCAP && r.contenu >= 0
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

fact ReceptacleNePeutPasAllerVersLuiMeme {
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

fact TousReceptaclesAccessibles{
	all r1,r2: Receptacle | some chemin: seq Receptacle | some r : Receptacle |
		/*last[chemin] != r && */last[chemin] = r1 && first[chemin] = r2  && r in chemin[idxOf[chemin,r]+1].listeRecep.elems =>
 		r in chemin.elems
}

fact CheminSansDoublons{
//	all d: Drone | ! hasDups[d.chemin]
	all d: Drone, t:Temps | # elems[d.chemin.t] = # inds[d.chemin.t]
}

fact PremierDuChemin{
	all d:Drone, t:Temps | some r: Receptacle | !d.chemin.t.isEmpty => (first[d.chemin.t]= r && distance[Entrepot.position, r.position] <= 3)
}
fact SecondDuChemin{
	all d:Drone, t:Temps | some r: Receptacle | !d.chemin.t.isEmpty => ((distance[r.position, Entrepot.position] > 0 && distance[r.position, Entrepot.position] <= 3) => d.chemin.t[1]=r)
}
fact DernierDuChemin{
	all d:Drone, t:Temps | !d.chemin.t.isEmpty => (last[d.chemin.t]= d.commande.destination.t)
}
fact CommandeUnSeulDrone{
	all disj d,d2:Drone, t:Temps | let c = d.commande | (c.destination.t != Entrepot &&c.contenu.t != 0)=>d.commande != d2.commande
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
		d.commande.destination.first = Entrepot
		d.chemin.first.isEmpty
	}
	all d:Drone, c:Commande | c.contenu.first = 0 => d.commande = c
	all c:Commande | c.contenu.first > 0 => c in Entrepot.ensembleCommandes.first
}

pred calculerChemin[d:Drone, t:Temps] {
	all r : Receptacle |
		/*last[d.chemin] != r && */
		r in d.chemin.t[idxOf[d.chemin.t,r]+1].listeRecep.elems
		=> r in d.chemin.t.elems
}

pred go {
	initialiser
	all t:Temps - last |let t'=t.next |
	{
		all d:Drone | bougerDrone[t,t',d]
		all c:Commande | bougerCommande[t,t',c]
	}
}

pred bougerDrone[t,t':Temps, d:Drone]{
	
	//majBatterie
	/*d.position.t' = d.position.t && some r:Receptacle | d.position.t = r.position => d.batterie.t' = d.batterie.t.add[1] else
	d.position.t' = d.position.t => d.batterie.t' = d.batterie.t else//immobile
	d.position.t' != d.position.t => d.batterie.t' = d.batterie.t.sub[1] //mouvement
	*/
	
	d.commande.contenu.t = 0 => {//Le contenu est vide
		d.position.t = Entrepot.position => { //entrepot
			some c:Commande | c in Entrepot.ensembleCommandes.t => {//il reste des commandes
				d.commande.destination.t' = c.destination.t
				d.commande.contenu.t' = c.contenu.t
				d.batterie.t'=d.batterie.t
				d.position.t'=d.position.t
				d.calculerChemin[t']
			}
		} /*else { // réceptacle destination
			d.commande.destination.contenu.t' = (d.commande.destination.contenu.t+d.commande.ensembleProd.t)//Le réceptacle change sa capacité
			d.commande.ensembleProd.t.contenu = 0
			d.position.t' = d.position.t => d.batterie.t' = d.batterie.t//immobile
		}*/
	}/*else{//Le drone n'est pas à destination
		intersectionVide[t,t',d,d.chemin.first.position] => { //Si on peut bouger, on le fait
		d.position.t' = d.chemin.first.position//on déplace le drone
		d.position.t' != d.position.t => d.batterie.t' = d.batterie.t.sub[1] //mouvement
		}
	}*/

}

pred bougerCommande[t,t':Temps, c:Commande]{
	c.contenu.t'=c.contenu.t
	c.destination.t'=c.destination.t
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

run go for 1 Drone, exactly 3 Receptacle, exactly 3 Commande,  6 Intersection, 7 int, exactly 3 Temps

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
