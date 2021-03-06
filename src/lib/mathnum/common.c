

/*
 * Authors: Tomi Jylhä-Ollila, Finland 2011-2014
 *          Ossi Saresoja, Finland 2009-2010
 *
 * This file is part of Kunquat.
 *
 * CC0 1.0 Universal, http://creativecommons.org/publicdomain/zero/1.0/
 *
 * To the extent possible under law, Kunquat Affirmers have waived all
 * copyright and related or neighboring rights to Kunquat.
 */


#include <math.h>

#include <debug/assert.h>
#include <mathnum/common.h>


bool is_p2(int64_t x)
{
    assert(x > 0);
    return (x & (x - 1)) == 0;
}


int64_t next_p2(int64_t x)
{
    assert(x > 0);

    x |= x >> 1;
    x |= x >> 2;
    x |= x >> 4;
    x |= x >> 8;
    x |= x >> 16;
    x |= x >> 32;

    return x + 1;
}


int64_t ceil_p2(int64_t x)
{
    assert(x > 0);

    if (is_p2(x))
        return x;

    return next_p2(x);
}


int64_t ipowi(int64_t base, int64_t exp)
{
    assert(exp >= 0);

    if (exp == 0)
        return 1;
    else if (exp % 2 == 0)
        return ipowi(base * base, exp / 2);

    return base * ipowi(base * base, exp / 2);
}


double powi(double x, int n)
{
    assert(n >= 0);

    double ret = 1.0;
    while (n > 0)
    {
        if ((n & 1) != 0)
            ret *= x;

        n >>= 1;
        x *= x;
    }

    return ret;
}


double sinc(double x)
{
    return (x == 0.0) ? 1.0 : (sin(x) / x);
}


