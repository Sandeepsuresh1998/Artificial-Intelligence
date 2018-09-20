#include "ClueReasoner.h"
#include <cstring> to sat_solver.cpp
#include <stdlib.h> to zchaff_dbase.cpp
using namespace std;

int ClueReasoner::GetPlayerNum(string player)
{	
	if (player == case_file)
		return num_players;
	
	for (int i = 0; i < num_players; i++)
		if (player == players[i])
			return i;
			
	cout<<"Illegal player: "<<player<<endl;
	return -1;
}

int ClueReasoner::GetCardNum(string card)
{
	for (int i = 0; i < num_cards; i++)
		if (card == cards[i])
			return i;
			
	cout<<"Illegal card: "<<card<<endl;
	return -1;
}

int ClueReasoner::GetPairNum(int player, int card) 
{
	return player * num_cards + card + 1;
}

int ClueReasoner::GetPairNum(string player, string card) 
{
	return GetPairNum(GetPlayerNum(player), GetCardNum(card));
}

int ClueReasoner::Query(string player, string card) 
{
	return solver->TestLiteral(GetPairNum(player,card));
}

string ClueReasoner::QueryString(int return_code)
{
	if (return_code == kFalse)
		return "n";
	else if (return_code == kTrue)
		return "Y";
	else if (return_code == kUnknown)
		return "-";
	else
		return "X";
}

void ClueReasoner::PrintNotepad()
{
	for (int i = 0; i < num_players; i++)
		cout<<"\t"<<players[i];
	cout<<"\t"<<case_file<<endl;
	
	for (int i = 0; i < num_cards; i++)
	{
		cout<<cards[i]<<"\t";
		for (int j = 0; j < num_players; j++)
			cout<<QueryString(Query(players[j], cards[i]))<<"\t";
		
		cout<<QueryString(Query(case_file, cards[i]))<<endl;
	}
}
	
void ClueReasoner::AddInitialClauses()
{
	/* The following code is given as an example to show how to create Clauses and post them to the solver. SatSolver.h uses the following typedefs:
		typedef int Literal;
		typedef std::vector<Literal> Clause;
		
	That is, a Literal (a propositional variable or its negation) is defined as a positive or a negative (meaning that it is in negated form, as in -p or -q) integer, and a Clause is defined as a vector of Literals.
	
	The function GetPairNum(p, c) returns the literal that corresponds to card c being at location p (either a player's or the case_file). 
	See ClueReasoner.h, lines 7-31 for a definition of the arrays and variables that you can use in your implementation. 
	*/

	// Each card is in at least one place (including the case file).
	for (int c = 0; c < num_cards; c++)	// Iterate over all cards.
	{
		Clause clause;
		for (int p = 0; p <= num_players; p++)	// Iterate over all players, including the case file (as a possible place for a card).
			clause.push_back(GetPairNum(p, c)); // Add to the clause the literal that states 'p has c'.
		
		solver->AddClause(clause);
	}
	
	// If a card is in one place, it cannot be in another place.
	// TO BE IMPLEMENTED AS AN EXERCISE

	for (int c = 0; c < num_cards; c++) // Iterate over all cards 
	{
		Clause clause;
		for (int p = 0; p <= num_players; p++) //It's equal to the num players because of the case file? 
		{
			//Player p has card c
			clause.push_back(GetPairNum(p,c));
			for (int k = 0; k <= num_players; k++) 
			{
				//Make sure we are not dealing with the same player
				if (k == p) 
				{
					continue;
				}
				else 
				{
					//Because player p has card c, player k cannot have card c
					clause.push_back(GetPairNum(k,c) * -1);
				}
			}
			solver->AddClause(clause);
		}
	}

	
	// At least one card of each category is in the case file.
	// TO BE IMPLEMENTED AS AN EXERCISE

	//Iterate through all player cards
	Clause sus_clause;
	for (int i = 0; i < num_suspects; i++) 
	{
		//Add clause that one player card is in the case file location
		sus_clause.push_back(GetPairNum(GetPlayerNum("cf"), GetCardNum(suspects[i])));
	}
	solver->AddClause(sus_clause);

	Clause weapon_clause;
	for (int i = 0; i < num_weapons; i++) 
	{
		//Add clause that at least one weapon is in casefile location
		weapon_clause.push_back(GetPairNum(GetPlayerNum("cf"), GetCardNum(weapons[i])));
	}
	solver->AddClause(weapon_clause);

	Clause room_clause;
	for (int i = 0; i < num_rooms; i++) 
	{
		//Add clause that at least one weapon is in casefile location
		room_clause.push_back(GetPairNum(GetPlayerNum("cf"), GetCardNum(rooms[i])));
	}
	solver->AddClause(room_clause);
 

//----------------------------------------------------------------------------------------------

	// No two cards in each category can both be in the case file.
	// TO BE IMPLEMENTED AS AN EXERCISE


	// No two cards for suspect category
	for (int i = 0; i < num_suspects; i++) 
	{
		Clause sus_clause;
		for (int k = 0; k < num_suspects; k++) 
		{
			if(i == k){
				continue;
			}
			//If suspect i, is in the casefile, then suspect k cannot be
			sus_clause.push_back(GetPairNum(GetPlayerNum("cf"), GetCardNum(suspects[i])));
			sus_clause.push_back(GetPairNum(GetPlayerNum("cf"), GetCardNum(suspects[k])) * -1);
		}
		solver->AddClause(sus_clause);
	}

	for (int i = 0; i < num_weapons; i++) 
	{
		Clause weapon_clause;
		for (int k = 0; k < num_weapons; k++) 
		{
			if(i == k)
			{
				continue;
			}
			//If weapon i, is in the casefile, then weapon k cannot be
			weapon_clause.push_back(GetPairNum(GetPlayerNum("cf"), GetCardNum(weapons[i])));
			weapon_clause.push_back(GetPairNum(GetPlayerNum("cf"), GetCardNum(weapons[k])) * -1);
		}
		solver->AddClause(weapon_clause);
	}

	for (int i = 0; i < num_rooms; i++) 
	{
		Clause room_clause;
		for (int k = 0; k < num_rooms; k++) 
		{
			if(i == k) 
			{
				continue;
			}
			//If room i, is in the casefile, then room k cannot be
			room_clause.push_back(GetPairNum(GetPlayerNum("cf"), GetCardNum(rooms[i])));
			room_clause.push_back(GetPairNum(GetPlayerNum("cf"), GetCardNum(rooms[k])) * -1);
		}
		solver->AddClause(room_clause);
	}



}

void ClueReasoner::Hand(string player, string cards[3])
{
	// GetPlayerNum returns the index of the player in the players array (not the suspects array). 
	// Remember that the players array is sorted wrt the order that the players play. 
	// Also note that, player_num (not to be confused with num_players) is a private variable of 
	// the ClueReasoner class that is initialized when this function is called.
	player_num = GetPlayerNum(player);
	// TO BE IMPLEMENTED AS AN EXERCISE

	// Now that we know the player_number we can adding clauses
	for (int c = 0; c < 3; c++) 
	{
		Clause clause;
		//My player has the card, so no one else can
		clause.push_back(GetPairNum(player_num, GetCardNum(cards[c])));
		solver->AddClause(clause);

		//My card cannot be in the case file
		Clause case_file_clause;
		case_file_clause.push_back(GetPairNum(GetPlayerNum("cf"), GetCardNum(cards[c])) * -1);
		solver->AddClause(clause);

		//Other players can't have my card
		for (int p = 0; p < num_players; p++) 
		{
			Clause clause;
			//If iterate to the player I am, let's continue
			cout << "GetPlayer: " << GetPlayerNum(players[p]) << " player num: " << player_num << endl;
			if(GetPlayerNum(players[p]) == player_num) 
			{
				continue;
			}

			// Every other player cannot have my card
			clause.push_back(GetPairNum(GetPlayerNum(players[p]), GetCardNum(cards[c])) * -1);
			solver->AddClause(clause);

		}
	}


}

void ClueReasoner::Suggest(string suggester, string card1, string card2, string card3, string refuter, string card_shown)
{
	// // Note that in the Java implementation, the refuter and the card_shown can be NULL. 
	// // In this C++ implementation, NULL is translated to be the empty string "".
	// // To check if refuter is NULL or card_shown is NULL, you should use if(refuter == "") or if(card_shown == ""), respectively.
	
	// TO BE IMPLEMENTED AS AN EXERCISE
	if(refuter != "") {
		cout << "LOL" << endl;
		if(card_shown != "") {
			//Immediately we know that refuter has card shown
			Clause refuter_clause;
			refuter_clause.push_back(GetPairNum(GetPlayerNum(refuter), GetCardNum(card_shown)));

			//QUESTION: Does saying one person has a card automatically maek it so that no other person has that card?
			//If not: TODO below.
			solver->AddClause(refuter_clause);
		} else {
			//Immediately we know that the refuter has at least one of the cards
			Clause refuter_clause;
			refuter_clause.push_back(GetPairNum(GetPlayerNum(refuter), GetCardNum(card1)));
			refuter_clause.push_back(GetPairNum(GetPlayerNum(refuter), GetCardNum(card2)));
			refuter_clause.push_back(GetPairNum(GetPlayerNum(refuter), GetCardNum(card3)));
			solver->AddClause(refuter_clause);
		}

		// NOTE: This is the section that is screwing things up
		//Finally we know that all the players in between suggester and refuter don't have card1, card2, or card3
		// int current_num = GetPlayerNum(suggester); // Getting the suggester's number
		// current_num++; //Starting with the player after suggester
		// int refuter_num = GetPlayerNum(refuter);
		// while(current_num != refuter_num) {
		// 	//If suggeter num went to the case file then we need to reset to 0
		// 	if(current_num == num_players) {
		// 		current_num = 0;
		// 		continue;
		// 	} 

		// 	//Need to add multiple clauses to show the current player doesn't have card1, card2, or card3
		// 	Clause card1_clause;
		// 	Clause card2_clause;
		// 	Clause card3_clause;


		// 	//The current player doesn't have any of the cards
		// 	card1_clause.push_back(GetPairNum(current_num, GetCardNum(card1) * -1));
		// 	card2_clause.push_back(GetPairNum(current_num, GetCardNum(card2) * -1));
		// 	card3_clause.push_back(GetPairNum(current_num, GetCardNum(card3) * -1));

		// 	solver->AddClause(card1_clause);
		// 	solver->AddClause(card2_clause);
		// 	solver->AddClause(card3_clause);

		// 	//Iterate to the next player 
		// 	current_num++;
		// } //End of section that is screwing things up

	} else {
		// cout << "Made it" << endl;
		// //Iterate through all players and say that they don't have the cards
		// for (int i = 0; i < num_players; i++) {
		// 	if (i == GetPlayerNum(suggester)) 
		// 		continue;

		// 	Clause card1_clause;
		// 	Clause card2_clause;
		// 	Clause card3_clause;

		// 	card1_clause.push_back(GetPairNum(i, GetCardNum(card1) * -1));
		// 	card2_clause.push_back(GetPairNum(i, GetCardNum(card2) * -1));
		// 	card3_clause.push_back(GetPairNum(i, GetCardNum(card3) * -1));

		// 	solver->AddClause(card1_clause);
		// 	solver->AddClause(card2_clause);
		// 	solver->AddClause(card3_clause);
		
	}
	
	
}

void ClueReasoner::Accuse(string suggester, string card1, string card2, string card3, bool is_correct)
{
	// TO BE IMPLEMENTED AS AN EXERCISE (you don't need to implement this)
}

