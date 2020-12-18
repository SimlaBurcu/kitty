/* kitty: C++ truth table library
 * Copyright (C) 2017-2020  EPFL
 *
 * Permission is hereby granted, free of charge, to any person
 * obtaining a copy of this software and associated documentation
 * files (the "Software"), to deal in the Software without
 * restriction, including without limitation the rights to use,
 * copy, modify, merge, publish, distribute, sublicense, and/or sell
 * copies of the Software, and to permit persons to whom the
 * Software is furnished to do so, subject to the following
 * conditions:
 *
 * The above copyright notice and this permission notice shall be
 * included in all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
 * EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES
 * OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
 * NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT
 * HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY,
 * WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
 * FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR
 * OTHER DEALINGS IN THE SOFTWARE.
 */

/*!
  \file threshold_identification.hpp
  \brief Threshold logic function identification

  \author CS-472 2020 Fall students
*/

#pragma once

#include <vector>
#include <lpsolve/lp_lib.h> /* uncomment this line to include lp_solve */
#include "traits.hpp"
#include "properties.hpp"
#include "isop.hpp"
#include "print.hpp"
namespace kitty
{

/*! \brief Threshold logic function identification

  Given a truth table, this function determines whether it is a threshold logic function (TF)
  and finds a linear form if it is. A Boolean function is a TF if it can be expressed as

  f(x_1, ..., x_n) = \sum_{i=1}^n w_i x_i >= T

  where w_i are the weight values and T is the threshold value.
  The linear form of a TF is the vector [w_1, ..., w_n; T].

  \param tt The truth table
  \param plf Pointer to a vector that will hold a linear form of `tt` if it is a TF.
             The linear form has `tt.num_vars()` weight values and the threshold value
             in the end.
  \return `true` if `tt` is a TF; `false` if `tt` is a non-TF.
*/
template<typename TT, typename = std::enable_if_t<is_complete_truth_table<TT>::value>>
bool is_threshold( const TT& tt, std::vector<int64_t>* plf = nullptr )
{
  auto numvars = tt.num_vars();
  std::vector<int64_t> linear_form(numvars + 1, 0);
  std::vector<int64_t> lp_solution;
  std::vector<bool> substituted(numvars, false);

  /* TODO */
  /* if tt is non-TF: */
  if(function_unateness(tt, substituted) == false){
    return false;
  }

  /* call the function f_star */
  TT f_star = tt;

  /* substitute x with x' */
  for ( auto i = 0u; i < numvars; ++i )
  {
    if(substituted[i])
      f_star = flip(f_star, i);
  }

  lprec *lp;
  REAL *row = NULL;
  int Ncol = numvars + 1; /* there are numvars + 1 (T)  variables in the model */
  int Nrow = numvars + 2; /* there are numvars variables in the model */

  lp = make_lp(0, Ncol);

  /* create space large enough for one row */
  row = (REAL *) calloc(Nrow, sizeof(*row));
  /* Onset and offset cubes */
  std::vector<cube> onSet = isop(f_star);
  std::vector<cube> offSet = isop(unary_not(f_star));

  /*********** print ISOP ***********/
  /*
  std::cout << "...on set..." << std::endl;
  for ( auto cube : onSet )
  {
    cube.print( tt.num_vars() );
    std::cout << std::endl;
  }
  std::cout << "... off set..." << std::endl;
  for ( auto cube : offSet )
  {
    cube.print( tt.num_vars() );
    std::cout << std::endl;
  }
  */
  /*********** print ISOP ***********/

  set_add_rowmode(lp, TRUE);  /* makes building the model faster if it is done rows by row */

  /* Positivity Constraints */
  /* For each variable we set a positivity constraint individually */
  for ( auto i = 0u; i < numvars + 1; i++ )
  {
    row[i + 1] = 1;
    add_constraint(lp, row,  GE, 0.0);
    row[i + 1] = 0;
  }

  /* Integer Constraints */
  for ( auto i = 1u; i < numvars + 2; i++ )
  {
    set_int(lp, i, TRUE);
  }

  /* ONSET Constraints */
  /* For each onset cube, we sum the weights of the variables that are part of
     the cube and not complemented. This sum must be greater than or equal to T
     get_bits Polarity bitmask of variables (0: negative, 1: positive)
     get_mask Care bitmask of variables (1: part of cube, 0: not part of cube)*/
   row[numvars + 1] = -1; //set T as the last element
   for( auto cube : onSet ){
     for ( auto i = 0u; i < numvars; i++ )
     {
       (cube.get_mask(i) && cube.get_bit(i)) ? (row[i + 1] = 1) : (row[i + 1] = 0);
     }
     /* add the row to lpsolve */
     add_constraint(lp, row, GE, 0.0);
   }

  /* OFFSET Constraints */
  /* For each offset cube, we sum the weights of the variables that are not part of
     the cube. This sum must be greater than or equal to T
     get_bits Polarity bitmask of variables (0: negative, 1: positive)
     get_mask Care bitmask of variables (1: part of cube, 0: not part of cube)*/
  for( auto cube : offSet ){
    for ( auto i = 0u; i < numvars; i++ )
    {
      (!cube.get_mask(i)) ? (row[i + 1] = 1) : (row[i + 1] = 0);
    }
    /* add the row to lpsolve */
    add_constraint(lp, row,  LE, -1.0);
  }
  set_add_rowmode(lp, FALSE);

  /* Objective Function */
   for ( auto i = 1u; i <= numvars + 1; ++i)
   {
     row[i] = 1;
   }
   set_obj_fn( lp, row );
   set_minim( lp );
   set_verbose( lp, IMPORTANT);
   //write_LP(lp, stdout);

   if (solve(lp)){
     return false;
   }

   get_variables(lp, row);
   for( auto i = 0; i < Ncol; i++ ){
     lp_solution.push_back(row[i]);
   }
   /* Derive a linear form of f from f_star */
   for( uint32_t i = 0; i < numvars; i++ ){
     if(substituted[i]){
       lp_solution[i] = -lp_solution[i]; //Substitute w_i with -w_i
       lp_solution[numvars] += lp_solution[i]; //subtract w_i from T
     }
   }
   linear_form = lp_solution;

   if ( plf )
   {
     *plf = linear_form;
   }

    /* free allocated memory and memory used by lpsolve */
    if(row != NULL)
      free(row);
    if(lp != NULL)
      delete_lp(lp);

    return true;
}

/*! \brief Checks whether a function is unate
  A function is positive unate if f(x') ≤ f(x) and  negative unate if f(x) ≤ f(x')
  \param tt Truth table
  \returns 2 if binate
*/
template<typename TT, typename = std::enable_if_t<is_complete_truth_table<TT>::value>>
bool function_unateness( const TT& tt, std::vector<bool>& substituted )
{
  auto numvars = tt.num_vars();

  for ( auto i = 0u; i < numvars; i++ ) //we check the unateness of f in each variable
  {
    auto const tt1 = cofactor0( tt, i );
    auto const tt2 = cofactor1( tt, i );


    if (is_unate_in_variable(tt1, tt2) == 0) //do nothing if positive unate
    {
      continue;
    }
    else if (is_unate_in_variable(tt1, tt2) == 1) //mark the variable to be substituted if negative unate
    {
      substituted[i] = true;
    }
    else //if the function is binate in any variable i we conclude that f is a non-TF
      return false;
  }
  return true;
}

/*! \brief Checks whether a function is unate in variable x
  A function is positive unate if f(x') ≤ f(x) and  negative unate if f(x) ≤ f(x')
  \param tt1 positive cofactor, tt2 negative cofactor, var_index variable
  \returns 0 if positive unate, 1 if negative unate, 2 if binate in variable x
*/
template<typename TT, typename = std::enable_if_t<is_complete_truth_table<TT>::value>>
uint8_t is_unate_in_variable( const TT& tt1, const TT& tt2)
{
  auto numvars = tt1.num_vars();

  uint8_t toret = 0; //start with assumption that positive unate

  for ( auto bit = 0; bit < ( 2 << ( numvars - 1 ) ); bit++ )
  {
    if (get_bit( tt1, bit ) == get_bit( tt2, bit ) ) //equal bits does not change unateness
    {
      continue;
    }
    else if (toret==0 && get_bit( tt1, bit ) < get_bit( tt2, bit ) ) //if toret is 0 this means that we did not encounter any bit position that will cause negative unateness and we check if the current bit position protects positive unateness
    {
      continue;
    }
    else if (get_bit( tt1, bit ) > get_bit( tt2, bit ) ) //if this condition holds, this means that the function is not postive unate, and we will check if negative unateness condition holds for the current bit position
    {
      toret = 1;
    }
    else //the function is binate in variable
      return 2;
  }

  return toret;
}

} /* namespace kitty */
