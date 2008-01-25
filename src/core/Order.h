

/*
 * Copyright 2008 Tomi Jylhä-Ollila
 *
 * This file is part of Kunquat.
 *
 * Kunquat is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * Kunquat is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with Kunquat.  If not, see <http://www.gnu.org/licenses/>.
 */


#ifndef K_ORDER_H
#define K_ORDER_H


#include <stdint.h>
#include <stdbool.h>

#include <Etable.h>


#define SUBSONGS_MAX (256)
#define PATTERNS_MAX (256)

#define ORDER_NONE (-1)


typedef struct Subsong
{
	int res;
	int16_t* pats;
} Subsong;


typedef struct Order
{
	Etable* subs;
} Order;


/**
 * Creates a new Order.
 *
 * \return   The new Order if successful, or \c NULL if memory allocation
 *           failed.
 */
Order* new_Order(void);


/**
 * Sets the pattern for the specified Order position.
 *
 * \param order     The Order -- must not be \c NULL.
 * \param subsong   The subsong number -- must be >= \c 0 and
 *                  < \c SUBSONGS_MAX.
 * \param index     The pattern index in the subsong -- must be >= \c 0 and
 *                  < \c PATTERNS_MAX.
 * \param pat       The pattern number -- must be >= \c 0 or ORDER_NONE.
 *
 * \return   \c true if successful, or \c false if memory allocation failed.
 */
bool Order_set(Order* order, uint16_t subsong, uint16_t index, int16_t pat);


/**
 * Gets the pattern from the specified Order position.
 *
 * \param order     The Order -- must not be \c NULL.
 * \param subsong   The subsong number -- must be >= \c 0 and
 *                  < \c SUBSONGS_MAX.
 * \param index     The pattern index in the subsong -- must be >= \c 0 and
 *                  < \c PATTERNS_MAX.
 *
 * \return   The pattern number if one exists, otherwise ORDER_NONE.
 */
int64_t Order_get(Order* order, uint16_t subsong, uint16_t index);


/**
 * Destroys an existing Order.
 *
 * \param order   The Order -- must not be \c NULL.
 */
void del_Order(Order* order);


#endif // K_ORDER_H

