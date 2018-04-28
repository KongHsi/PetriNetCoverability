# PetriNetCoverability

TODO: 
  1. Something wrong with 
 
      } while ((new_R != R)); 
      } while ((new_R != R) && (new_R != Cudd_ReadLogicZero(gbm)));
   
      The second line doesn't really work.
      
  2. Program crashes if the bad state is reaching the ceil. For example 15, and 15 is already the possible max state.
