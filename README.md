# PetriNetCoverability

TODO: 
  1. Something wrong with 
 
      } while ((new_R != R)); 
      } while ((new_R != R) && (new_R != Cudd_ReadLogicZero(gbm)));
   
      The second line doesn't really work. Something wrong with backward_reachability function. If I keep 1, then it's possible we get 0 for R, but if I keep 2, then it's just not working properly. Verification always fails.
      
  2. Program crashes if the bad state is reaching the ceil. For example 15, and 15 is already the possible max state.
  
  3. What should initial weight be?
