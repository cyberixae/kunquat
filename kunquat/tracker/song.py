
class Song():

    def __init__(self, composition, song_id):
        self._song_id = song_id
        path = song_id
        self._view = composition.get_view(path)

    def get_name(self):
        name = self._view.get_json('m_name.json') or '-'
        return name

    def _count_each(self, l):
        counters = {}
        for item in l:
            try:
                value = counters[item]
            except KeyError:
                value = 0
            yield [item, value]
            counters[item] = value + 1
        
    def get_order_list(self):
        if 'p_orderlist.json' not in self._view.keys():
            songdata = self._view.get_json('p_song.json')
            old_list = songdata['patterns']
            instances = list(self._count_each(old_list))
            self._view.put('p_orderlist.json', instances)
        orderlist = self._view.get_json('p_orderlist.json')
        return orderlist
