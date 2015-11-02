#ifndef SYMMETRY_H
#define SYMMETRY_H

#include <map>
#include <string>

#include "symmetry/bliss/graph.hh"
#include "logics/Logic.h"
#include "pterms/Pterm.h"

namespace symmetry 
{


	class Detector {
		
		//for a cleaner interface (?)
		typedef unsigned int GraphNode;
		

		public:

			typedef std::vector<unsigned int> Cycle;

			Detector(Logic&, PTRef&);
			~Detector();
			void toDot(const std::string path);
			void findSBPs();
			inline PTRef getSBPs() { return sbps; }
			static const unsigned int ARGUMENT_NODES_COLOR = 1;
			
			//Functor for easy permutation cycle filtering
			class CycleFilter {

				const bliss::Digraph<PTRef>* graph;
				Logic& logic;

				public:
					CycleFilter(const bliss::Digraph<PTRef>* g, Logic& l):
						graph(g), logic(l) {}

					bool operator()(const Cycle&);
			}; 

		private:
			
			class GraphCache {
				public:
					std::map<std::string, GraphNode> symbolNodes;
					std::map<PTRef, GraphNode> rootNodes;
					std::map<std::pair<PTRef, PTRef>, GraphNode> argumentNodes;
					
					std::map<std::string, unsigned int> symbolSortColors;
					std::map<std::string, unsigned int> rootSortColors;
			};
			friend class GraphCache; //do I really need this?

			unsigned int nextColor;
			bliss::Digraph<PTRef>* graph;
			PTRef& term;
			Logic& logic;
			GraphCache cache;
			PTRef sbps;
			
			GraphNode addSymbolNode(const PTRef&);
			GraphNode addRootNode(const PTRef&);
			GraphNode addArgumentNode(const PTRef& term, const PTRef& parent);
			
			//TODO: shouldn't this be moved to Pterm.h/c?			
			bool commutes(const PTRef&);

			static void computeSBPs(void*, unsigned int, const unsigned int*);

	};
}

#endif /* SYMMETRY_H */
