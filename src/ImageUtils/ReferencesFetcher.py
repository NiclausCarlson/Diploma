from ImageUtils.ObjectFetcher import ObjectFetcher
from ImageUtils.PlaneFetcher import PlaneFetcher
from ImageUtils.ReferenceMarker import ReferenceMarker


class ReferencesFetcher:
    def __init__(self):
        self.object_fetcher = ObjectFetcher()
        self.plane_fetcher = PlaneFetcher()
        self.reference_marker = ReferenceMarker()

    def fetch(self, video, object_name):
        obj = self.object_fetcher.fetch_from_video(video, object_name)
        plane = self.plane_fetcher.fetch(obj)
        return self.reference_marker.get_marked(plane, None)
