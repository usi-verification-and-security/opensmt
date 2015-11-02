#include "Symmetry.h"
#include <stack>
#include <algorithm>
#include "symmetry/bliss/utils.hh"
#include "bliss/graph.cc"
#include "Vec.h"

namespace bliss
{
	template class Digraph<PTRef>;
}

namespace symmetry 
{

	//C++11 only
	//using Cycle = std::vector<unsigned int>;

	//C++98 compatible
	//typedef std::vector<unsigned int> Cycle;
	
	// Detector::HookParams::HookParams(const bliss::Digraph<PTRef>& g, Logic& l, PTRef& f) :
	// 								 graph(g), 
	// 								 logic(l), 
	// 								 formula(f) {}

	/*
		Permutation cycle filtering criterion
	*/
	bool Detector::CycleFilter::operator()(const Detector::Cycle& cycle) {
		if(cycle.size() != 2) { return true; }

	 	const PTRef* t1 = graph->get_vertex_value(cycle[0]);
		const PTRef* t2 = graph->get_vertex_value(cycle[1]);
	 	SRef sort1 = logic.getSortRef(*t1);
		SRef sort2 = logic.getSortRef(*t2);

		return !(logic.hasSortBool(*t1) && sort1 == sort2);
	}
	
	Detector::Detector(Logic& l, PTRef& formula) : 
			  nextColor(ARGUMENT_NODES_COLOR),
			  graph( new bliss::Digraph<PTRef>() ),
			  term(formula),
			  logic(l),
			  sbps(PTRef_Undef)
	{

		bliss::Digraph<PTRef>::SplittingHeuristic shs_directed = bliss::Digraph<PTRef>::shs_fsm;
		graph->set_splitting_heuristic(shs_directed);

		std::stack<PTRef*> terms;
		terms.push(&term);
		
		while(!terms.empty()) {
			
			PTRef& currentRef = *(terms.top());
			Pterm& current = logic.getPterm(currentRef);
			std::string symbol = logic.getSymName(currentRef);
			terms.pop();

			//if the unique symbol is not already in the graph, add it
			//Detector::GraphNode symbolNode{addSymbolNode(currentRef, logic)};
			Detector::GraphNode rootNode = addRootNode(currentRef);

			if(current.nargs()) //if arity > 0
			{
				Detector::GraphNode root_node = addRootNode(currentRef);

				if(commutes(currentRef)) 
				{
					//std::cerr << " ; The term " << symbol << " commutes" << std::endl;
 					for(int i = 0; i < current.size(); ++i)
					{
						const PTRef& ti = current[i];
						Detector::GraphNode ti_root_node = addRootNode(ti);
						graph->add_edge(root_node, ti_root_node);
					}
				}
				else 
				{
					//TODO: ugly, think of how to fix this
					//this is necessary because if the term has only one arg it won't enter the next loop
					if(current.size() == 1)
					{
						const PTRef& ti = current[0];
						Detector::GraphNode ti_arg_node = addArgumentNode(ti, currentRef);
						graph->add_edge(root_node, ti_arg_node);						
					}

					for(int i = 0; i < current.size()-1; ++i)
					{
						const PTRef& ti 	  = current[i];
						const PTRef& ti_p_one = current[i+1];
						Detector::GraphNode ti_arg_node = addArgumentNode(ti, currentRef);
						Detector::GraphNode ti_p_one_arg_node = addArgumentNode(ti_p_one, currentRef);
						graph->add_edge(ti_arg_node, ti_p_one_arg_node);
						if(i == 0) { graph->add_edge(root_node, ti_arg_node); }
					}
				}
			}

			for(int i = 0; i < current.size(); ++i) {
				PTRef* c = &(current[i]);
				terms.push(c);
			}
		}
	}

	Detector::~Detector()
	{
		delete graph;
		//graph = nullptr;
		graph = NULL;
	}

	/**
		Exports the generated graph to file in dot format
	*/
	void Detector::toDot(const std::string path)
	{
		FILE* file = fopen(path.c_str(), "w");
		if(file != NULL) {
                    graph->write_dot(file);
                    fclose(file);
                }
		//file = nullptr;
		file = NULL;	
	}

	/***
		Utility to compute the cycle form of a permutation
		TODO: discuss with antti if it would be better to return a pointer to a vector
		instead of returning by value
	*/
	static std::vector<Detector::Cycle> computePermCycles(const unsigned int size, const unsigned int* perm)
	{
		assert(size > 0);
		assert(perm);

		std::vector<Detector::Cycle> cycles;

		for(unsigned int i = 0; i < size; i++) {
	  	
	    	unsigned int j = perm[i];
	    	
	    	if(j == i) { continue; }
	    	
	    	bool is_first = true;
	    	while(j != i) {
	      		if(j < i) {
	        		is_first = false;
	        		break;
	      		}
	      		j = perm[j];
	    	}
	    	
	    	if(!is_first) { continue; }
	  		
	  		Detector::Cycle cycle;
	  		cycle.push_back(i);
	    	
	    	j = perm[i];
	    	while(j != i) {
	      	
	    		cycle.push_back(j);
	        	j = perm[j];
	      	
	    	}
	    	
	    	cycles.push_back(cycle);
	  }
	  return cycles;
	}

	/**
		Computes the SBPs from a generator.

		param must be pointing to a Detector instance.
	*/
	void Detector::computeSBPs(void *param, unsigned int n, const unsigned int *aut)
	{
		//std::cerr << "; Helloooooo" << std::endl;
  		assert(param);
  		//Detector::HookParams* params = static_cast<Detector::HookParams*>(param);
  		Detector* params = static_cast<Detector*>(param);
  		std::vector<Detector::Cycle> cycles = computePermCycles(n,aut);

  		const bliss::Digraph<PTRef>* graph = params->graph;
  		Logic& logic = params->logic;
  		PTRef& formula = params->term;

  		//filter only the "interesting" cycles
  		cycles.erase(
    		std::remove_if(cycles.begin(), cycles.end(),
     //    	[&](const Cycle & c) { 
     //     		 	if(c.size() != 2) { return true; }

	 			// 	const PTRef* t1 = graph->get_vertex_value(c[0]);
					// const PTRef* t2 = graph->get_vertex_value(c[1]);
	 			// 	SRef sort1 = logic.getSortRef(*t1);
					// SRef sort2 = logic.getSortRef(*t2);

					// return !(logic.hasSortBool(*t1) && sort1 == sort2);
     //    	}),
    		Detector::CycleFilter(graph, logic)),
    		cycles.end()); 

  		vec<PTRef> sbps;

  		//TODO: refactor this loop in separate function?
  		//for i in {0..n}
  		for(unsigned int i=0; i<cycles.size(); ++i)
  		{
  			Detector::Cycle ci = cycles[i];
  			const PTRef* pi = graph->get_vertex_value(ci[0]);
  			const PTRef* qi = graph->get_vertex_value(ci[1]);

  			vec<PTRef> rhsTerms;
  			rhsTerms.push(*pi);
  			rhsTerms.push(*qi);
  			PTRef rhs = logic.mkImpl(rhsTerms);

  			if(i==0) { //special case, only rhs of the SBP

  				sbps.push(rhs);
  				
  			} else {
  				
  				vec<PTRef> lhsTerms;
  				for(unsigned int j=0; j<i; ++j)
  				{
  					Detector::Cycle cj = cycles[j];
  					const PTRef* pj = graph->get_vertex_value(cj[0]);
  					const PTRef* qj = graph->get_vertex_value(cj[1]);
  					vec<PTRef> eq;
  					eq.push(*pj);
  					eq.push(*qj);
  					PTRef con = logic.mkEq(eq);
  					lhsTerms.push(con);
  				}
  				PTRef lhs = logic.mkAnd(lhsTerms);
				vec<PTRef> final;
				final.push(lhs);
				final.push(rhs);
				PTRef sbp = logic.mkImpl(final);
				sbps.push(sbp);
  			}
  		}

  		if(params->sbps != PTRef_Undef) 
  		{
  			sbps.push(params->sbps);
  		}
  		params->sbps = logic.mkAnd(sbps); 

  		//bliss::print_permutation(stderr, n, aut, 0);
  		//fprintf(stderr, "\n");
	}

	/**
		Augments the formula passed to Detector with the symmetry breaking predicates
	*/
	void Detector::findSBPs()
	{
		bliss::Stats stats;
		//HookParams* params = new HookParams(*graph, logic, term);
		void* hookParams = static_cast<void*>(this);
		graph->find_automorphisms(stats, &Detector::computeSBPs, hookParams);
		//delete params;
	}

	/**
		Adds a unique symbol node to the graph, or returns it if already exists
	*/
	Detector::GraphNode Detector::addSymbolNode(const PTRef& term) 
	{	
		std::string symbol = logic.getSymName(term);
		if(!cache.symbolNodes.count(symbol)) 
		{
			//std::cout << "Adding symbol node for " << symbol << "\n";
			unsigned int color;
			//coloring uninterpreted node
			if(logic.isUF(term) || logic.isUP(term) || logic.isBoolAtom(term)) 
			{
				//if I already assigned a color to this sort I retrieve it else I create one
				//std::cerr << "Term " << logic.printTerm(term) << " is uninterpreted\n";
				SRef sortRef = logic.getSortRef(term);
				std::string sortName = logic.getSortName(sortRef);
				color = ((cache.symbolSortColors.count(sortName)) ? 
				 	   	 cache.symbolSortColors[sortName] : 
				 	     ++nextColor);

				cache.symbolSortColors[sortName] = color;
			}
			else 
			{ 
				//std::cerr << "; Term " << logic.printTerm(term) << " is interpreted\n";
				color = ++nextColor;
			}

			//const PTRef *termRef{&term};
			Detector::GraphNode symNode= graph->add_vertex(color, symbol, &term);
			//std::cerr << "; [" << symNode << "] " << "Added symbol node " << symbol << std::endl;
			
			cache.symbolNodes[symbol] = symNode;
			return symNode;
		}
		return cache.symbolNodes[symbol];
	}

	/**
		Adds a root node for a term to the graph, or return it if already inserted
	*/
	Detector::GraphNode Detector::addRootNode(const PTRef& term) 
	{
		if(!cache.rootNodes.count(term)) 
		{

			const Pterm& current = logic.getPterm(term);
			SRef sortRef = logic.getSortRef(term);
			std::string symbol = logic.getSymName(term);
			std::string sortName = logic.getSortName(sortRef);

			//root nodes get a color based on their sort
			unsigned int color = ((cache.rootSortColors.count(sortName)) ? cache.rootSortColors[sortName] : ++nextColor);
			cache.rootSortColors[sortName] = color;

			//retrieve symbol node
			//Detector::GraphNode symbolNode{addSymbolNode(term, logic)};
			//Detector::GraphNode rootNode{ (current.nargs() == 0) ? symbolNode : graph->add_vertex(color, symbol) };
			const PTRef* termRef{&term};
			Detector::GraphNode rootNode = graph->add_vertex(color, symbol, &term);
			//std::cerr << "; [" << rootNode << "] " << "Added root node " << symbol << std::endl;
			
			if(current.nargs() > 0) 
			{ 
				Detector::GraphNode symbolNode = addSymbolNode(term);
				graph->add_edge(rootNode, symbolNode); 
			} 
			else //this node is also the symbol node for the term 
			{
				//std::cerr << "; [" << rootNode << "] " << "Symbold node for  " << symbol << " is also symbol node" << std::endl;
				cache.symbolNodes[symbol] = rootNode;
				
				//if symbol node is interpreted, change the color to a unique one
				if(!(logic.isUF(term) || logic.isUP(term) || logic.isBoolAtom(term))) {
					unsigned int newColor = ++nextColor;
					graph->change_color(rootNode, newColor);
				} 
				//else it is uninterpreted, so set it as the color for symbol nodes of the same sort
				//or should I leave it as the color for root nodes of the same sort?
				//(ambiguous in the algorithm description which one gets the priority)
				else {
					color = ((cache.symbolSortColors.count(sortName)) ? 
				 	   	 cache.symbolSortColors[sortName] : 
				 	     ++nextColor);
					cache.symbolSortColors[sortName] = color;
					graph->change_color(rootNode, color);
				}
				
			}

			cache.rootNodes[term] = rootNode;
		}
		
		return cache.rootNodes[term];
	}

	/**
		Adds an argument node for an argument to the graph, or return it if already inserted
	*/
	Detector::GraphNode Detector::addArgumentNode(const PTRef& term, const PTRef& parent)
	{

		std::pair<PTRef, PTRef> key = std::make_pair(term, parent);
		std::string symbol = logic.getSymName(term);

		if(!cache.argumentNodes.count(key))
		{
			const PTRef* termRef = &term;
			//add argument node with specific unique color
			Detector::GraphNode argumentNode = graph->add_vertex(ARGUMENT_NODES_COLOR, symbol, &term);
			//std::cerr << "; [" << argumentNode << "] " << "Added symbol node " << symbol << std::endl;

			cache.argumentNodes[key] = argumentNode;

			//get root node
			Detector::GraphNode rootNode = addRootNode(term);

			//connect argument node to root node
			graph->add_edge(argumentNode, rootNode);
			return argumentNode;
		}
		return cache.argumentNodes[key];
	}

	/**
		Check if a term commutes
	*/
	bool Detector::commutes(const PTRef& term)
	{
		return logic.commutes(logic.getSymRef(term));
	}

}
